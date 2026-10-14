"""Shopify -> Odoo Online real-time order sync.

Receives Shopify order webhooks (orders/create, orders/updated,
orders/cancelled), verifies the HMAC signature, and creates/updates the
matching sale.order in Odoo via XML-RPC.

Idempotent: matches existing orders by client_order_ref = Shopify's order
"name" (e.g. "#1001"), so Shopify's at-least-once delivery retries never
create duplicates.

Required environment variables (set these in Railway's dashboard, never
commit real values to git):
    ODOO_URL       e.g. https://920d-custom.odoo.com
    ODOO_DB        e.g. 920d-custom
    ODOO_LOGIN     e.g. bheller@920dcustom.com
    ODOO_PASSWORD  Odoo password or API key
    SHOPIFY_WEBHOOK_SECRET   from Shopify admin's webhook settings

Optional -- only needed for the /dashboard read-only sync-status page:
    SHOPIFY_STORE_DOMAIN    e.g. 920d.myshopify.com
    SHOPIFY_CLIENT_ID       from the Shopify Dev Dashboard custom app
    SHOPIFY_CLIENT_SECRET   from the same app
    DASHBOARD_PASSWORD      HTTP Basic Auth password for /dashboard
"""
import base64
import hashlib
import hmac
import json
import os
import time
import urllib.error
import urllib.parse
import urllib.request
import xmlrpc.client
from datetime import datetime, timedelta

from flask import Flask, Response, request, jsonify

app = Flask(__name__)

ODOO_URL = os.environ["ODOO_URL"]
ODOO_DB = os.environ["ODOO_DB"]
ODOO_LOGIN = os.environ["ODOO_LOGIN"]
ODOO_PASSWORD = os.environ["ODOO_PASSWORD"]
SHOPIFY_WEBHOOK_SECRET = os.environ["SHOPIFY_WEBHOOK_SECRET"]

SHOPIFY_STORE_DOMAIN = os.environ.get("SHOPIFY_STORE_DOMAIN")
SHOPIFY_CLIENT_ID = os.environ.get("SHOPIFY_CLIENT_ID")
SHOPIFY_CLIENT_SECRET = os.environ.get("SHOPIFY_CLIENT_SECRET")
DASHBOARD_PASSWORD = os.environ.get("DASHBOARD_PASSWORD")
SHOPIFY_API_VERSION = "2024-10"

_common = xmlrpc.client.ServerProxy(f"{ODOO_URL}/xmlrpc/2/common", allow_none=True)
_uid = _common.authenticate(ODOO_DB, ODOO_LOGIN, ODOO_PASSWORD, {})
_models = xmlrpc.client.ServerProxy(f"{ODOO_URL}/xmlrpc/2/object", allow_none=True)


def odoo(model, method, args, kwargs=None):
    return _models.execute_kw(ODOO_DB, _uid, ODOO_PASSWORD, model, method, args, kwargs or {})


def odoo_safe(model, method, args, kwargs=None):
    """Some Odoo action methods (reconcile, the invoice-wizard action, etc)
    return a value that fails XML-RPC marshalling even though the
    server-side action succeeded -- swallow only that specific failure."""
    try:
        return odoo(model, method, args, kwargs)
    except Exception as e:
        if "cannot marshal None" in str(e):
            return None
        raise


def verify_hmac(raw_body: bytes, hmac_header: str) -> bool:
    digest = hmac.new(SHOPIFY_WEBHOOK_SECRET.encode("utf-8"), raw_body, hashlib.sha256).digest()
    computed = base64.b64encode(digest).decode()
    return hmac.compare_digest(computed, hmac_header or "")


def find_or_create_partner(shopify_order):
    email = (shopify_order.get("email") or shopify_order.get("contact_email")
             or (shopify_order.get("customer") or {}).get("email"))
    if not email:
        return None

    existing = odoo("res.partner", "search", [[("email", "=", email)]], {"limit": 1})
    if existing:
        return existing[0]

    customer = shopify_order.get("customer") or {}
    shipping = shopify_order.get("shipping_address") or {}
    name = " ".join(filter(None, [customer.get("first_name"), customer.get("last_name")])).strip() or email

    vals = {
        "name": name,
        "email": email,
        "phone": shipping.get("phone") or shopify_order.get("phone") or "",
        "street": shipping.get("address1") or "",
        "street2": shipping.get("address2") or "",
        "city": shipping.get("city") or "",
        "zip": shipping.get("zip") or "",
    }
    country_code = shipping.get("country_code")
    if country_code:
        country = odoo("res.country", "search", [[("code", "=", country_code)]], {"limit": 1})
        if country:
            vals["country_id"] = country[0]
            state_code = shipping.get("province_code")
            if state_code:
                state = odoo("res.country.state", "search", [
                    [("country_id", "=", country[0]), ("code", "=", state_code)]
                ], {"limit": 1})
                if state:
                    vals["state_id"] = state[0]
    return odoo("res.partner", "create", [vals])


def line_discount_percent(item):
    """Real per-line discount %, computed from Shopify's own discount_allocations
    (exact dollar amount actually taken off this line) -- never guessed/assumed,
    works the same regardless of how the discount was applied (code, app,
    automatic) or what rate it happens to be."""
    price = float(item.get("price") or 0.0)
    qty = item.get("quantity") or 1
    list_total = price * qty
    if list_total <= 0:
        return 0.0
    discount_total = sum(float(a.get("amount") or 0.0) for a in (item.get("discount_allocations") or []))
    return round((discount_total / list_total) * 100, 2)


def order_discount_source(shopify_order):
    """Human-readable label for WHY a discount was applied, so Odoo can
    distinguish a dealer/wholesale order from a one-off site promo. Prefers
    an explicit signal (order tags naming the wholesale app) over guessing;
    falls back to the real discount code/title Shopify used; blank if no
    discount was applied at all."""
    if not any(float(li.get("total_discount") or 0.0) > 0 for li in shopify_order.get("line_items", [])):
        return False

    tags = (shopify_order.get("tags") or "").lower()
    if "wholesale" in tags or "dealer" in tags:
        # Report the actual observed rate rather than hardcoding 40 -- if the
        # program's rate ever changes, this stays accurate automatically.
        items = shopify_order.get("line_items", [])
        pct = round(sum(line_discount_percent(i) for i in items) / len(items), 1) if items else 0
        return f"Dealer {pct:g}%"

    for app in shopify_order.get("discount_applications", []):
        code = app.get("code") or app.get("title")
        if code:
            return f"Promo: {code}"

    return "Website discount"


def get_or_create_product(sku, item):
    """Look up a product by SKU; if it genuinely doesn't exist in Odoo yet,
    create a minimal placeholder instead of silently dropping the product
    link (the historical bug this guards against: 38 old orders ended up
    with unmatched-SKU lines that never got fixed because nothing flagged
    them). The placeholder has no cost/category/BOM -- it's deliberately
    bare so it's obviously incomplete, not mistaken for a real finished
    catalog entry."""
    found = odoo("product.template", "search", [[("default_code", "=", sku)]], {"limit": 1})
    if found:
        return found[0], False
    new_id = odoo("product.template", "create", [{
        "name": item.get("name") or item.get("title") or sku,
        "default_code": sku,
        "is_storable": True,
        "sale_ok": True,
        "list_price": float(item.get("price") or 0.0),
    }])
    return new_id, True


def build_order_lines(shopify_order, new_products):
    """new_products is a list the caller passes in and this appends to --
    any SKU that had to be auto-created gets recorded there so the caller
    can post a visible chatter warning on the order (see
    _warn_new_products below)."""
    lines = []
    for item in shopify_order.get("line_items", []):
        sku = item.get("sku")
        product_id = None
        if sku:
            product_id, was_created = get_or_create_product(sku, item)
            if was_created:
                new_products.append(sku)
        line_vals = {
            "name": item.get("name") or item.get("title") or sku or "Shopify line item",
            "product_uom_qty": item.get("quantity") or 1,
            "price_unit": float(item.get("price") or 0.0),
            "discount": line_discount_percent(item),
            # Force no tax: products are intentionally configured with no
            # sales tax (Shopify is the system of record for tax actually
            # collected), but Odoo's automated tax engine will otherwise
            # inject a tax guess despite the empty product config.
            "tax_ids": [(6, 0, [])],
        }
        if product_id:
            line_vals["product_id"] = product_id
        lines.append((0, 0, line_vals))
    return lines


def warn_new_products(order_id, new_products):
    if not new_products:
        return
    skus = ", ".join(new_products)
    try:
        odoo_safe("sale.order", "message_post", [[order_id]], {
            "body": (f"⚠️ Auto-created new product(s) for SKU(s) not yet in Odoo: "
                     f"{skus}. No cost, category, or BOM set yet -- needs review."),
        })
    except Exception:
        pass  # warning is best-effort -- never block the real order sync over it


def find_existing_order(order_ref):
    found = odoo("sale.order", "search", [[("client_order_ref", "=", order_ref)]], {"limit": 1})
    return found[0] if found else None


def extract_tracking(shopify_order):
    """Pull the tracking number/company off the first fulfillment with one,
    if any. Shopify puts real fulfillment data (tracking_company,
    tracking_number) in the order payload's fulfillments array once shipped."""
    for f in shopify_order.get("fulfillments", []):
        tracking_number = f.get("tracking_number") or (f.get("tracking_numbers") or [None])[0]
        tracking_company = f.get("tracking_company")
        if tracking_number:
            return tracking_number, tracking_company
    return None, None


_CARRIER_CACHE = {}


def find_carrier_id(tracking_company, shopify_order):
    """Match Shopify's free-text tracking_company to one of our configured
    delivery.carrier records (each has a real tracking_url template), so
    Odoo's computed Tracking URL actually populates. USPS/FedEx have
    separate Domestic/International carriers -- picked via the shipping
    country. Returns None (not fatal) if nothing matches -- the tracking
    number itself still gets saved either way."""
    if not tracking_company:
        return None

    if not _CARRIER_CACHE:
        for c in odoo("delivery.carrier", "search_read", [[]], {"fields": ["id", "name"]}):
            _CARRIER_CACHE[c["name"]] = c["id"]

    company = tracking_company.lower()
    is_us = (shopify_order.get("shipping_address") or {}).get("country_code") == "US"

    if "usps" in company or "postal" in company:
        return _CARRIER_CACHE.get("USPS Domestic" if is_us else "USPS International")
    if "fedex" in company:
        return _CARRIER_CACHE.get("Fedex US" if is_us else "Fedex International")
    if "ups" in company:
        return _CARRIER_CACHE.get("UPS")
    return None


def try_ship_delivery(order_id, shopify_order=None):
    """Validate the order's real delivery (actually deducts on-hand stock)
    if there's enough quantity to fully cover it -- matches real-world
    reality for a live order (unlike the historical backfill, which
    deliberately avoided real stock movement since that history was already
    baked into current on-hand counts). If stock is short, don't force it
    negative -- flag x_delivery_review_needed and leave it for manual
    review. QuickBooks remains the source of truth for inventory in the
    meantime, so an occasional gap here isn't catastrophic, just needs a
    human look."""
    pickings = odoo("stock.picking", "search_read",
        [[("sale_id", "=", order_id), ("state", "not in", ("done", "cancel"))]],
        {"fields": ["id", "move_ids"]})
    if not pickings:
        return

    move_ids = [m for p in pickings for m in p["move_ids"]]
    if not move_ids:
        return
    moves = odoo("stock.move", "read", move_ids, {"fields": ["id", "product_id", "product_uom_qty"]})

    product_ids = list({m["product_id"][0] for m in moves})
    qty_available = {p["id"]: p["qty_available"] for p in odoo("product.product", "read", [product_ids], {"fields": ["qty_available"]})}

    # Sum demand per product across all moves on this order, in case the
    # same product appears on more than one line/move.
    demand_by_product = {}
    for m in moves:
        pid = m["product_id"][0]
        demand_by_product[pid] = demand_by_product.get(pid, 0) + m["product_uom_qty"]

    if any(qty_available.get(pid, 0) < qty for pid, qty in demand_by_product.items()):
        odoo("sale.order", "write", [[order_id], {"x_delivery_review_needed": True}])
        return

    # carrier_tracking_url is a read-only field computed from carrier_id's
    # tracking_url template + carrier_tracking_ref -- setting both is what
    # actually makes the clickable link populate, not just the ref alone.
    tracking_number, tracking_company = extract_tracking(shopify_order or {})
    carrier_id = find_carrier_id(tracking_company, shopify_order or {})

    for m in moves:
        odoo("stock.move", "write", [[m["id"]], {"quantity": m["product_uom_qty"]}])
    for p in pickings:
        if tracking_number:
            update_vals = {"carrier_tracking_ref": tracking_number}
            if carrier_id:
                update_vals["carrier_id"] = carrier_id
            odoo("stock.picking", "write", [[p["id"]], update_vals])
        try:
            odoo("stock.picking", "button_validate", [[p["id"]]])
        except Exception:
            odoo("sale.order", "write", [[order_id], {"x_delivery_review_needed": True}])


BACKORDER_MO_CAP = 10


def split_into_batches(qty, cap=BACKORDER_MO_CAP):
    """15 -> [10, 5]; 25 -> [10, 10, 5]."""
    batches = []
    remaining = qty
    while remaining > 0:
        batch = min(cap, remaining)
        batches.append(batch)
        remaining -= batch
    return batches


def create_backorder_mos(order_id, order_ref):
    """Create an MO for the full ordered quantity of every storable line on
    order_id -- deliberately ignores on-hand stock entirely (Bennett wants
    a build order for what was sold, every time, not just the shortfall).
    Safe to call more than once: dedups on (origin, product_id) rather than
    sale_line_id, because draft-order edits fully delete+recreate
    sale.order.line rows (see the (5,0,0) rebuild above), which would make
    a sale_line_id-keyed dedup check silently miss."""
    order_lines = odoo("sale.order.line", "search_read",
        [[("order_id", "=", order_id), ("product_id", "!=", False)]],
        {"fields": ["id", "product_id", "product_uom_qty"]})
    if not order_lines:
        return

    product_ids = list({l["product_id"][0] for l in order_lines})
    products = {p["id"]: p for p in odoo("product.template", "read",
        [product_ids], {"fields": ["is_storable", "uom_id"]})}

    origin = f"Shopify backorder: {order_ref}"

    for line in order_lines:
        product_id = line["product_id"][0]
        product = products.get(product_id)
        if not product or not product["is_storable"]:
            continue  # service products excluded -- can't manufacture those

        qty_ordered = line["product_uom_qty"] or 0
        if qty_ordered <= 0:
            continue

        already = odoo("mrp.production", "search",
            [[("origin", "=", origin), ("product_id", "=", product_id)]], {"limit": 1})
        if already:
            continue

        for batch_qty in split_into_batches(qty_ordered):
            # Left in "draft" deliberately -- Bennett wants "Confirmed" (=
            # Awaiting Build) to mean the work order has actually been
            # printed and handed to the floor. Draft MOs can still be
            # printed fine; a person clicks Odoo's native "Confirm" button
            # once they've done that, which is what moves it into the
            # Awaiting Build queue the scanning app looks for.
            odoo("mrp.production", "create", [{
                "product_id": product_id,
                "product_qty": batch_qty,
                # Odoo Online (saas~19.4) uses "uom_id" here -- a documented
                # field-name drift from other Odoo versions that use
                # "product_uom_id" for the same concept.
                "uom_id": product["uom_id"][0],
                "origin": origin,
                "sale_line_id": line["id"],
                # Native "Sale" smart button on the MO reads sale_line_id
                # directly and already works. x_sale_order_id is a custom
                # field that drives the reverse direction (a "Manufacturing
                # Orders" section on the Sale Order form) since Odoo's own
                # mrp_production_count/ids there are computed through the
                # procurement/stock-move chain, which this catalog doesn't
                # use yet (no BOM routing configured).
                "x_sale_order_id": order_id,
            }])


_MISC_JOURNAL_ID = None
_SHOPIFY_BANK_ACCOUNT_ID = None


def _misc_journal_id():
    global _MISC_JOURNAL_ID
    if _MISC_JOURNAL_ID is None:
        _MISC_JOURNAL_ID = odoo("account.journal", "search", [[("code", "=", "MISC")]], {"limit": 1})[0]
    return _MISC_JOURNAL_ID


def _shopify_bank_account_id():
    global _SHOPIFY_BANK_ACCOUNT_ID
    if _SHOPIFY_BANK_ACCOUNT_ID is None:
        _SHOPIFY_BANK_ACCOUNT_ID = odoo("account.account", "search", [[("name", "=", "920D Shopify")]], {"limit": 1})[0]
    return _SHOPIFY_BANK_ACCOUNT_ID


def auto_invoice_and_pay(order_id, order_ref):
    """Shopify has already collected real payment for this order --
    financial_status is exactly "paid" by the time this is called (checked
    by the caller). Odoo should reflect that immediately instead of
    sitting in "To Invoice"/"Not Paid" waiting on someone to click through
    the invoice + register-payment flow by hand for every single order.

    Creates a regular invoice (sale.advance.payment.inv wizard -- the
    underlying _create_invoices is a private method, not RPC-callable) for
    the full order, posts it, then settles it with a direct reconciling
    journal entry against the "920D Shopify" account (the real payout
    account Shopify Payments deposits into). Deliberately NOT using
    account.payment/Register Payment here -- verified directly (2026-09)
    that it only flips payment_state to "in_payment" without actually
    reconciling the AR line (amount_residual stays untouched), even on a
    clean single-invoice test with no historical data involved. The manual
    settlement-move-and-reconcile approach is the one proven to actually
    zero out the residual, throughout this whole migration project.
    """
    wiz_ctx = {"active_model": "sale.order", "active_ids": [order_id], "active_id": order_id}
    wiz_id = odoo("sale.advance.payment.inv", "create", [{"advance_payment_method": "delivered"}], {"context": wiz_ctx})
    odoo_safe("sale.advance.payment.inv", "create_invoices", [[wiz_id]], {"context": wiz_ctx})

    invoices = odoo("account.move", "search_read",
        [[("invoice_origin", "=", order_ref), ("move_type", "=", "out_invoice"), ("state", "=", "draft")]],
        {"fields": ["id"]})
    for inv in invoices:
        inv_id = inv["id"]
        odoo("account.move", "action_post", [[inv_id]])
        ar_lines = odoo("account.move.line", "search_read",
            [[("move_id", "=", inv_id), ("account_id.account_type", "=", "asset_receivable")]],
            {"fields": ["id", "account_id", "partner_id", "debit", "credit"]})
        if not ar_lines:
            continue
        amt = sum(l["debit"] - l["credit"] for l in ar_lines)
        if abs(amt) < 0.01:
            continue
        settle_id = odoo("account.move", "create", [{
            "journal_id": _misc_journal_id(),
            "ref": f"Shopify auto-pay for {order_ref}",
            "line_ids": [
                (0, 0, {"account_id": _shopify_bank_account_id(), "name": "Shopify auto-payment", "debit": amt, "credit": 0.0}),
                (0, 0, {"account_id": ar_lines[0]["account_id"][0], "partner_id": ar_lines[0]["partner_id"][0] if ar_lines[0]["partner_id"] else False,
                        "name": "Shopify auto-payment", "debit": 0.0, "credit": amt}),
            ],
        }])
        odoo("account.move", "action_post", [[settle_id]])
        settle_line = odoo("account.move.line", "search_read",
            [[("move_id", "=", settle_id), ("account_id.account_type", "=", "asset_receivable")]], {"fields": ["id"]})[0]
        odoo_safe("account.move.line", "reconcile", [[l["id"] for l in ar_lines] + [settle_line["id"]]])


def total_refunded(shopify_order):
    """Sum of all successful refund transactions Shopify has recorded
    against this order so far. Shopify's order payload carries a growing
    "refunds" array (one entry per refund event, each with its own
    transactions) -- this is always the cumulative total, not just the
    latest refund, which is why the caller diffs it against
    x_refunded_amount rather than treating it as a delta directly."""
    total = 0.0
    for refund in shopify_order.get("refunds", []):
        for txn in refund.get("transactions", []):
            if txn.get("kind") == "refund" and txn.get("status") == "success":
                total += float(txn.get("amount") or 0.0)
    return total


def process_refund(order_id, order_ref, refund_amount):
    """Mirror image of auto_invoice_and_pay: issues a credit note for the
    refunded amount against the original invoice, then settles it with a
    reversing journal entry showing the cash actually leaving the "920D
    Shopify" payout account back to the customer. Only meaningful once the
    order's already been through auto_invoice_and_pay (there must be a
    posted invoice to credit against) -- a no-op otherwise."""
    orig_invoice = odoo("account.move", "search_read",
        [[("invoice_origin", "=", order_ref), ("move_type", "=", "out_invoice"), ("state", "=", "posted")]],
        {"fields": ["id", "partner_id"], "limit": 1})
    if not orig_invoice:
        return
    inv = orig_invoice[0]

    credit_note_id = odoo("account.move", "create", [{
        "move_type": "out_refund",
        "partner_id": inv["partner_id"][0],
        "invoice_origin": order_ref,
        "ref": f"Shopify refund for {order_ref}",
        "invoice_line_ids": [(0, 0, {
            "name": f"Shopify refund for {order_ref}",
            "quantity": 1,
            "price_unit": refund_amount,
            "tax_ids": [(6, 0, [])],
        })],
    }])
    odoo("account.move", "action_post", [[credit_note_id]])

    cn_ar = odoo("account.move.line", "search_read",
        [[("move_id", "=", credit_note_id), ("account_id.account_type", "=", "asset_receivable")]],
        {"fields": ["id", "account_id"]})
    if not cn_ar:
        return

    settle_id = odoo("account.move", "create", [{
        "journal_id": _misc_journal_id(),
        "ref": f"Shopify refund settlement for {order_ref}",
        "line_ids": [
            (0, 0, {"account_id": cn_ar[0]["account_id"][0], "partner_id": inv["partner_id"][0],
                    "name": "Shopify refund", "debit": refund_amount, "credit": 0.0}),
            (0, 0, {"account_id": _shopify_bank_account_id(), "name": "Shopify refund", "debit": 0.0, "credit": refund_amount}),
        ],
    }])
    odoo("account.move", "action_post", [[settle_id]])
    settle_ar = odoo("account.move.line", "search_read",
        [[("move_id", "=", settle_id), ("account_id.account_type", "=", "asset_receivable")]], {"fields": ["id"]})[0]
    odoo_safe("account.move.line", "reconcile", [[l["id"] for l in cn_ar] + [settle_ar["id"]]])


def cancel_or_flag_mos(order_ref):
    """Shopify order cancellations have no equivalent for a build that's
    already in progress or finished -- so this splits on MO state instead
    of blindly cancelling: anything not yet built is safe to cancel
    outright (the floor should stop), anything already "done" gets a
    chatter flag instead since the physical item (and the builder's pay
    for it) already exists and needs a human decision, not a silent
    deletion."""
    origin = f"Shopify backorder: {order_ref}"
    mos = odoo("mrp.production", "search_read", [[("origin", "=", origin)]], {"fields": ["id", "state", "name"]})
    for mo in mos:
        if mo["state"] == "done":
            odoo_safe("mrp.production", "message_post", [[mo["id"]]], {
                "body": f"Shopify order {order_ref} was cancelled AFTER this build was already marked Done -- review whether it needs to be reworked or returned to stock."
            })
        elif mo["state"] != "cancel":
            try:
                odoo("mrp.production", "write", [[mo["id"]], {"state": "cancel"}])
            except Exception:
                odoo_safe("mrp.production", "message_post", [[mo["id"]]], {
                    "body": f"Shopify order {order_ref} was cancelled but this MO could not be auto-cancelled -- needs manual review."
                })


def find_order_by_shopify_id(shopify_order_id):
    if not shopify_order_id:
        return None
    found = odoo("sale.order", "search", [[("x_shopify_order_id", "=", str(shopify_order_id))]], {"limit": 1})
    return found[0] if found else None


def describe_return_items(payload):
    items = []
    for li in payload.get("return_line_items", []):
        qty = li.get("quantity")
        reason = li.get("return_reason") or ""
        items.append(f"{qty}x (reason: {reason})" if reason else f"{qty}x")
    return ", ".join(items) if items else "(no line item detail)"


def handle_return_webhook(topic, payload):
    """Returns only get visibility (chatter note + a flag) here, never an
    automatic stock/refund action -- a returned item needs physical
    inspection before it's safe to say it's resellable, and the actual
    money movement still arrives separately through the normal refund
    path (total_refunded/process_refund above) once Shopify issues it.
    Silently no-ops if the order predates x_shopify_order_id being
    tracked (set at order creation, see shopify_webhook below) -- nothing
    to attach the note to in that case."""
    order_id = find_order_by_shopify_id(payload.get("order_id"))
    if not order_id:
        return

    items_desc = describe_return_items(payload)
    return_name = payload.get("name") or payload.get("id")

    if topic == "returns/request":
        odoo("sale.order", "write", [[order_id], {"x_has_open_return": True}])
        body = f"Shopify return {return_name} requested: {items_desc}. Awaiting approval."
    elif topic == "returns/approve":
        body = f"Shopify return {return_name} approved: {items_desc}. Awaiting item(s) back."
    elif topic == "returns/decline":
        odoo("sale.order", "write", [[order_id], {"x_has_open_return": False}])
        body = f"Shopify return {return_name} declined: {items_desc}."
    elif topic == "returns/cancel":
        odoo("sale.order", "write", [[order_id], {"x_has_open_return": False}])
        body = f"Shopify return {return_name} was cancelled."
    elif topic == "returns/close":
        odoo("sale.order", "write", [[order_id], {"x_has_open_return": False}])
        body = (f"Shopify return {return_name} closed: {items_desc}. "
                f"Any refund is handled separately via the normal refund sync.")
    else:
        return

    odoo_safe("sale.order", "message_post", [[order_id]], {"body": body})


@app.route("/webhook/shopify", methods=["POST"])
def shopify_webhook():
    raw_body = request.get_data()
    hmac_header = request.headers.get("X-Shopify-Hmac-Sha256", "")
    if not verify_hmac(raw_body, hmac_header):
        return jsonify({"error": "invalid signature"}), 401

    topic = request.headers.get("X-Shopify-Topic", "")
    payload = json.loads(raw_body)

    # Returns are a separate Shopify resource, not an Order payload -- their
    # JSON only carries the numeric order_id (never the order name/number),
    # so this is handled entirely separately from the order-sync logic
    # below, matched via x_shopify_order_id instead of client_order_ref.
    if topic.startswith("returns/"):
        try:
            handle_return_webhook(topic, payload)
            return jsonify({"status": "ok", "topic": topic}), 200
        except Exception as e:
            return jsonify({"error": str(e)}), 500

    order_ref = payload.get("name") or str(payload.get("id"))

    # In-person sales are handled entirely in Odoo's own POS app, not synced
    # from Shopify -- skip anything that came from Shopify POS so the two
    # never double-book the same physical sale.
    if (payload.get("source_name") or "").lower() == "pos":
        return jsonify({"status": "skipped", "reason": "pos order, handled natively in Odoo", "order_ref": order_ref}), 200

    try:
        if topic == "orders/cancelled":
            existing_id = find_existing_order(order_ref)
            if existing_id:
                existing = odoo("sale.order", "read", [[existing_id]], {"fields": ["x_invoice_checked", "amount_total"]})[0]
                cancel_or_flag_mos(order_ref)
                if existing["x_invoice_checked"] and existing["amount_total"]:
                    # Odoo blocks cancelling an order that's already been
                    # invoiced -- a full reversing credit note is the real
                    # equivalent (same mechanism as a partial refund, just
                    # for the whole amount) instead of letting this throw.
                    try:
                        process_refund(existing_id, order_ref, existing["amount_total"])
                        odoo("sale.order", "write", [[existing_id], {"x_refunded_amount": existing["amount_total"]}])
                        odoo_safe("sale.order", "message_post", [[existing_id]], {
                            "body": "Shopify cancelled this order after it was already invoiced -- issued a full reversing credit note instead of blocking the cancel."
                        })
                    except Exception as e:
                        odoo_safe("sale.order", "message_post", [[existing_id]], {
                            "body": f"Shopify cancelled this order but the reversing credit note failed ({str(e)[:300]}) -- needs manual review."
                        })
                else:
                    try:
                        odoo("sale.order", "action_cancel", [[existing_id]])
                    except Exception as e:
                        odoo_safe("sale.order", "message_post", [[existing_id]], {
                            "body": f"Shopify cancelled this order but Odoo could not auto-cancel it ({str(e)[:300]}) -- needs manual review."
                        })
            return jsonify({"status": "cancelled", "order_ref": order_ref}), 200

        existing_id = find_existing_order(order_ref)
        partner_id = find_or_create_partner(payload)
        if not partner_id:
            return jsonify({"error": "no customer email on order"}), 400

        discount_source = order_discount_source(payload)
        new_products = []

        if existing_id:
            existing = odoo("sale.order", "read", [[existing_id]], {"fields": ["state", "x_invoice_checked", "x_backorder_checked", "x_refunded_amount"]})[0]
            existing_state = existing["state"]
            invoice_checked = existing["x_invoice_checked"]
            backorder_checked = existing["x_backorder_checked"]
            already_refunded = existing["x_refunded_amount"] or 0.0
            update_vals = {"partner_id": partner_id, "x_discount_source": discount_source}
            if existing_state == "draft":
                # Safe to fully rebuild lines only pre-confirmation -- Odoo
                # blocks removing lines from a confirmed order (invoicing/
                # delivery tracking), so confirmed orders keep their
                # original lines and only get header fields refreshed here.
                update_vals["order_line"] = [(5, 0, 0)] + build_order_lines(payload, new_products)
            odoo("sale.order", "write", [[existing_id], update_vals])
            new_id = existing_id
        else:
            invoice_checked = False
            backorder_checked = False
            already_refunded = 0.0
            new_id = odoo("sale.order", "create", [{
                # Explicitly set name = order_ref so the Odoo order number
                # IS the Shopify order number (e.g. "920-36218") instead of
                # Odoo's own auto-generated S00001-style sequence. This only
                # bypasses the sequence for this one record -- it keeps
                # counting normally for anything else that doesn't set name.
                "name": order_ref,
                "partner_id": partner_id,
                "client_order_ref": order_ref,
                "x_discount_source": discount_source,
                # Stored so a later Return webhook (a separate Shopify
                # resource that only carries the numeric order_id, never
                # the human-readable order name/number) can find this
                # order directly -- no callback to Shopify's API needed.
                "x_shopify_order_id": str(payload.get("id") or ""),
                "order_line": build_order_lines(payload, new_products),
            }])
        warn_new_products(new_id, new_products)

        financial_status = payload.get("financial_status")
        if financial_status in ("paid", "partially_paid") or payload.get("confirmed"):
            try:
                odoo("sale.order", "action_confirm", [[new_id]])
            except Exception:
                pass  # already confirmed or not confirmable yet -- not fatal

            # Only start production once payment is real -- avoids committing
            # shop floor capacity to orders that might not go through. Gated
            # on x_backorder_checked (not "is this a new order") so a
            # mid-request failure-and-retry doesn't silently skip it forever.
            if not backorder_checked:
                create_backorder_mos(new_id, order_ref)
                odoo("sale.order", "write", [[new_id], {"x_backorder_checked": True}])

            # Only auto-invoice+pay on a real, fully-paid order -- a
            # partially_paid order genuinely only has PART of the money in,
            # so auto-marking the whole invoice paid would misrepresent
            # reality. Gated on x_invoice_checked (not "is this new") so a
            # mid-request failure-and-retry doesn't silently skip it forever.
            if financial_status == "paid" and not invoice_checked:
                try:
                    auto_invoice_and_pay(new_id, order_ref)
                except Exception:
                    pass  # invoicing issue -- not fatal, doesn't block the order sync itself
                odoo("sale.order", "write", [[new_id], {"x_invoice_checked": True}])

        # Refunds (full or partial) land as orders/updated webhooks with a
        # growing "refunds" array and financial_status flipped to
        # "refunded"/"partially_refunded" -- handled independently of the
        # block above since a refund can arrive well after the order was
        # paid+invoiced, with financial_status no longer even "paid" by
        # then. Only meaningful once there's a real invoice to credit
        # against (invoice_checked), and diffed against what's already
        # been processed so Shopify's at-least-once retries never double
        # the reversal.
        if invoice_checked:
            refunded_now = total_refunded(payload)
            delta = refunded_now - already_refunded
            if delta > 0.01:
                try:
                    process_refund(new_id, order_ref, delta)
                    odoo("sale.order", "write", [[new_id], {"x_refunded_amount": refunded_now}])
                except Exception as e:
                    odoo_safe("sale.order", "message_post", [[new_id]], {
                        "body": f"Shopify refund of ${delta:.2f} could not be auto-reconciled ({str(e)[:300]}) -- needs manual review."
                    })

        # "Completed" = locked. An order is only truly done once it's fully
        # paid AND fully shipped -- partial payment or partial fulfillment
        # doesn't count. Checked on every delivery (create + updates) since
        # fulfillment almost always happens via a later orders/updated
        # webhook, not the initial create. Idempotent: writing locked=True
        # on an already-locked order is a harmless no-op.
        if financial_status == "paid" and payload.get("fulfillment_status") == "fulfilled":
            try:
                try_ship_delivery(new_id, payload)
            except Exception:
                pass  # delivery issue -- not fatal, doesn't block the order sync itself
            try:
                odoo("sale.order", "write", [[new_id], {"locked": True}])
            except Exception:
                pass  # not confirmed yet or otherwise not lockable -- not fatal

        return jsonify({"status": "ok", "order_ref": order_ref, "odoo_order_id": new_id}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500


def shopify_access_token():
    """Dev Dashboard custom apps (required for any new custom app since
    Shopify retired legacy custom apps in Jan 2026) don't hand out a
    static Admin API token -- this requests a fresh one via the client
    credentials grant every time instead. It's valid 24h, but re-fetching
    per dashboard load is simpler and cheap enough not to bother caching."""
    data = urllib.parse.urlencode({
        "grant_type": "client_credentials",
        "client_id": SHOPIFY_CLIENT_ID,
        "client_secret": SHOPIFY_CLIENT_SECRET,
    }).encode()
    req = urllib.request.Request(f"https://{SHOPIFY_STORE_DOMAIN}/admin/oauth/access_token", data=data)
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read())["access_token"]


def fetch_recent_shopify_orders(token, days):
    """Paginates via the Link header's rel="next" URL -- Shopify's REST
    cursor-based pagination requires following that exact URL rather than
    constructing subsequent pages manually (page_info tokens aren't
    reusable across different query params)."""
    since = (datetime.utcnow() - timedelta(days=days)).strftime("%Y-%m-%dT%H:%M:%SZ")
    url = (f"https://{SHOPIFY_STORE_DOMAIN}/admin/api/{SHOPIFY_API_VERSION}/orders.json"
           f"?status=any&limit=250&created_at_min={urllib.parse.quote(since)}")
    orders = []
    while url:
        req = urllib.request.Request(url, headers={"X-Shopify-Access-Token": token})
        with urllib.request.urlopen(req, timeout=20) as resp:
            link_header = resp.headers.get("Link", "") or ""
            data = json.loads(resp.read())
        orders.extend(data.get("orders", []))
        url = None
        for part in link_header.split(","):
            if 'rel="next"' in part:
                url = part.split(";")[0].strip().strip("<> ")
    return orders


def shopify_order_url(shopify_id):
    handle = (SHOPIFY_STORE_DOMAIN or "").replace(".myshopify.com", "")
    return f"https://admin.shopify.com/store/{handle}/orders/{shopify_id}"


def odoo_order_url(odoo_id):
    return f"{ODOO_URL}/web#model=sale.order&view_type=form&id={odoo_id}"


def audit_sync(days):
    token = shopify_access_token()
    shopify_orders = [so for so in fetch_recent_shopify_orders(token, days)
                       if (so.get("source_name") or "").lower() != "pos"]
    names = [so["name"] for so in shopify_orders]

    # Not checking invoice status here -- most orders are never meant to
    # get a formal Odoo invoice (Shopify/its payment processor is already
    # the real financial record for them), so "not invoiced" on its own
    # isn't a sync problem worth flagging.
    odoo_orders = odoo("sale.order", "search_read", [[("name", "in", names)]], {"fields": [
        "id", "name", "state", "locked",
        "x_refunded_amount", "x_delivery_review_needed", "x_has_open_return",
    ]}) if names else []
    odoo_by_name = {o["name"]: o for o in odoo_orders}
    odoo_ids = [o["id"] for o in odoo_orders]

    unmatched_lines = odoo("sale.order.line", "search_read",
        [[("order_id", "in", odoo_ids), ("display_type", "=", False), ("product_id", "=", False)]],
        {"fields": ["order_id", "name"]}) if odoo_ids else []
    unmatched_by_order = {}
    for l in unmatched_lines:
        unmatched_by_order.setdefault(l["order_id"][0], []).append(l["name"])

    rows = []
    for so in shopify_orders:
        name = so["name"]
        fin = so.get("financial_status")
        fulfillment = so.get("fulfillment_status")
        oo = odoo_by_name.get(name)
        issues = []

        if not oo:
            issues.append("Missing from Odoo entirely")
        else:
            if fin in ("paid", "partially_paid") and oo["state"] == "draft":
                issues.append(f"Shopify is {fin} but Odoo order is still draft")
            if fin == "paid" and fulfillment == "fulfilled" and not oo["locked"]:
                issues.append("Fulfilled in Shopify but not marked shipped in Odoo")
            if oo["x_delivery_review_needed"]:
                issues.append("Flagged in Odoo for delivery review")
            shopify_refunded = total_refunded(so)
            odoo_refunded = oo["x_refunded_amount"] or 0.0
            if abs(shopify_refunded - odoo_refunded) > 0.01:
                issues.append(f"Refund mismatch: Shopify ${shopify_refunded:.2f} vs Odoo ${odoo_refunded:.2f}")
            if oo["x_has_open_return"]:
                issues.append("Has an open Shopify return")
            unmatched = unmatched_by_order.get(oo["id"], [])
            if unmatched:
                issues.append(f"Unmatched SKU line(s): {', '.join(unmatched)}")

        customer = so.get("customer") or {}
        customer_name = " ".join(filter(None, [customer.get("first_name"), customer.get("last_name")])).strip()
        email = so.get("email") or customer.get("email") or ""

        rows.append({
            "name": name,
            "shopify_id": so.get("id"),
            "odoo_id": oo["id"] if oo else None,
            "financial_status": fin,
            "fulfillment_status": fulfillment,
            "total": so.get("total_price"),
            "customer_name": customer_name,
            "email": email,
            "created_at": (so.get("created_at") or "")[:10],
            "in_odoo": bool(oo),
            "issues": issues,
        })
    return rows


DASHBOARD_CSS = """
body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Arial, sans-serif; margin: 0; padding: 24px; color: #1a1a1a; background: #f6f6f7; }
h1 { font-size: 20px; margin: 0 0 20px; }
.cards { display: flex; gap: 12px; margin-bottom: 20px; }
.card { background: #fff; border: 1px solid #e3e3e3; border-radius: 10px; padding: 14px 20px; min-width: 110px; }
.card .num { font-size: 26px; font-weight: 650; display: block; }
.card .label { font-size: 12px; color: #6d7175; text-transform: uppercase; letter-spacing: .03em; }
.card.flagged .num { color: #d72c0d; }
.card.clean .num { color: #008060; }
.toolbar { display: flex; gap: 10px; align-items: center; margin-bottom: 16px; flex-wrap: wrap; background: #fff; border: 1px solid #e3e3e3; border-radius: 10px; padding: 12px 14px; }
.toolbar input[type=text], .toolbar select, .toolbar input[type=number] { padding: 7px 10px; border: 1px solid #c9cccf; border-radius: 6px; font-size: 13px; }
.toolbar input[type=text] { flex: 1; min-width: 180px; }
.toolbar button { padding: 7px 14px; border-radius: 6px; border: 1px solid #c9cccf; background: #fff; cursor: pointer; font-size: 13px; }
.toolbar button.primary { background: #008060; color: #fff; border-color: #008060; }
table { border-collapse: collapse; width: 100%; font-size: 13px; background: #fff; border-radius: 10px; overflow: hidden; border: 1px solid #e3e3e3; }
td, th { padding: 9px 12px; text-align: left; vertical-align: top; border-bottom: 1px solid #ededed; }
th { background: #fafafa; color: #6d7175; font-size: 11px; text-transform: uppercase; letter-spacing: .03em; position: sticky; top: 0; }
tr:last-child td { border-bottom: none; }
tr.row-flagged { background: #fff6f5; }
tr:hover { background: #f1f6ff !important; }
.issues { color: #d72c0d; }
.issues.ok { color: #008060; }
.links a { margin-right: 8px; font-size: 12px; }
.badge { display: inline-block; padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 600; white-space: nowrap; }
.badge-green { background: #d7f5e9; color: #006e43; }
.badge-yellow { background: #fff2cc; color: #946800; }
.badge-red { background: #fde3e0; color: #a0290f; }
.badge-gray { background: #eceef0; color: #5c5f62; }
.badge-blue { background: #e0edff; color: #1b4db3; }
.muted { color: #8c9196; font-size: 12px; }
"""

FINANCIAL_BADGE = {
    "paid": "green", "partially_paid": "yellow", "pending": "blue", "authorized": "blue",
    "refunded": "gray", "partially_refunded": "yellow", "voided": "red",
}
FULFILLMENT_BADGE = {"fulfilled": "green", "partial": "yellow"}


def badge(text, color_map):
    color = color_map.get(text, "gray")
    label = (text or "unfulfilled").replace("_", " ")
    return f'<span class="badge badge-{color}">{label}</span>'


def render_table_section(rows, days):
    """Just the summary cards + toolbar + table -- shared by the standalone
    /dashboard page and the embedded /app page (which fetches this
    fragment client-side and injects it, since the embedded shell itself
    has to load before App Bridge can even produce a session token to
    authenticate the data request with). Filtering itself is wired up by
    a small script living in each OUTER page template, not here --
    <script> tags inside HTML set via innerHTML never execute, so the
    filter logic has to live outside this fragment."""
    clean = sum(1 for r in rows if not r["issues"])
    flagged = len(rows) - clean
    body_rows = []
    for r in sorted(rows, key=lambda r: (not r["issues"], r["name"])):
        issues_html = "<br>".join(r["issues"]) if r["issues"] else "OK"
        issues_class = "issues" if r["issues"] else "issues ok"
        links = [f'<a href="{shopify_order_url(r["shopify_id"])}" target="_top">Shopify</a>']
        if r["odoo_id"]:
            links.append(f'<a href="{odoo_order_url(r["odoo_id"])}" target="_top">Odoo</a>')
        search_blob = " ".join([r["name"], r["customer_name"] or "", r["email"] or ""]).lower()
        body_rows.append(
            f'<tr class="{"row-flagged" if r["issues"] else ""}" '
            f'data-flagged="{1 if r["issues"] else 0}" '
            f'data-financial="{r["financial_status"] or ""}" '
            f'data-fulfillment="{r["fulfillment_status"] or "unfulfilled"}" '
            f'data-search="{search_blob}">'
            f'<td><b>{r["name"]}</b><div class="muted">{r["created_at"]}</div></td>'
            f'<td>{r["customer_name"] or "-"}<div class="muted">{r["email"] or ""}</div></td>'
            f'<td>{badge(r["financial_status"], FINANCIAL_BADGE)}</td>'
            f'<td>{badge(r["fulfillment_status"], FULFILLMENT_BADGE)}</td>'
            f'<td>${r["total"]}</td>'
            f'<td class="links">{"".join(links)}</td>'
            f'<td class="{issues_class}">{issues_html}</td></tr>'
        )
    return f"""<div class="cards">
<div class="card"><span class="num">{len(rows)}</span><span class="label">Orders checked</span></div>
<div class="card flagged"><span class="num">{flagged}</span><span class="label">Flagged</span></div>
<div class="card clean"><span class="num">{clean}</span><span class="label">Clean</span></div>
</div>
<div class="toolbar">
  <form method="get" style="display:flex;gap:8px;align-items:center;margin:0;">
    <span class="muted">Days back</span>
    <input type="number" name="days" value="{days}" style="width:70px">
    <button type="submit" class="primary">Refresh</button>
  </form>
  <input type="text" id="f-search" placeholder="Search order #, customer, email...">
  <select id="f-flag"><option value="">All rows</option><option value="1">Flagged only</option><option value="0">Clean only</option></select>
  <select id="f-financial"><option value="">Any payment status</option><option value="paid">Paid</option><option value="partially_paid">Partially paid</option><option value="pending">Pending</option><option value="refunded">Refunded</option><option value="partially_refunded">Partially refunded</option><option value="voided">Voided</option></select>
  <select id="f-fulfillment"><option value="">Any fulfillment</option><option value="fulfilled">Fulfilled</option><option value="partial">Partial</option><option value="unfulfilled">Unfulfilled</option></select>
</div>
<table id="sync-table"><thead><tr><th>Order</th><th>Customer</th><th>Payment</th><th>Fulfillment</th><th>Total</th><th>Links</th><th>Issues</th></tr></thead>
<tbody>
{''.join(body_rows)}
</tbody></table>"""


FILTER_JS = """
function wireFilters() {
  const search = document.getElementById('f-search');
  const flag = document.getElementById('f-flag');
  const financial = document.getElementById('f-financial');
  const fulfillment = document.getElementById('f-fulfillment');
  if (!search) return;
  function apply() {
    const q = search.value.toLowerCase();
    const rows = document.querySelectorAll('#sync-table tbody tr');
    rows.forEach(function(row) {
      const matchesSearch = !q || row.dataset.search.includes(q);
      const matchesFlag = !flag.value || row.dataset.flagged === flag.value;
      const matchesFinancial = !financial.value || row.dataset.financial === financial.value;
      const matchesFulfillment = !fulfillment.value || row.dataset.fulfillment === fulfillment.value;
      row.style.display = (matchesSearch && matchesFlag && matchesFinancial && matchesFulfillment) ? '' : 'none';
    });
  }
  [search, flag, financial, fulfillment].forEach(function(el) { el.addEventListener('input', apply); });
}
"""


def render_dashboard(rows, days):
    return f"""<!doctype html><html><head><meta charset="utf-8">
<title>920D Shopify/Odoo Sync Status</title>
<style>{DASHBOARD_CSS}</style></head><body>
<h1>920D Shopify &harr; Odoo Sync Status</h1>
{render_table_section(rows, days)}
<script>{FILTER_JS}
document.addEventListener('DOMContentLoaded', wireFilters);
wireFilters();
</script>
</body></html>"""


def check_dashboard_auth():
    auth = request.authorization
    if not DASHBOARD_PASSWORD or not auth or not hmac.compare_digest(auth.password, DASHBOARD_PASSWORD):
        return False
    return True


@app.route("/dashboard", methods=["GET"])
def dashboard():
    if not check_dashboard_auth():
        return Response("Authentication required", 401, {"WWW-Authenticate": 'Basic realm="920D Sync Dashboard"'})
    if not (SHOPIFY_STORE_DOMAIN and SHOPIFY_CLIENT_ID and SHOPIFY_CLIENT_SECRET):
        return jsonify({"error": "Shopify API credentials not configured on this server"}), 500
    days = min(int(request.args.get("days", 60)), 365)
    try:
        rows = audit_sync(days)
    except urllib.error.HTTPError as e:
        return jsonify({"error": f"Shopify API error: {e.code} {e.read().decode()[:500]}"}), 502
    return Response(render_dashboard(rows, days), mimetype="text/html")


def _b64url_decode(s):
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


def verify_shopify_id_token(token):
    """Manual HS256 JWT verification (no PyJWT dependency, consistent with
    the rest of this project's minimal-dependency style) of the App
    Bridge session token Shopify signs with our own Client Secret.
    Mirrors Shopify's documented embedded-app verification: signature,
    audience, expiry/not-before, and iss/dest hostname match (proves the
    token was actually issued for a page embedded in OUR shop's admin,
    not replayed from somewhere else)."""
    try:
        header_b64, payload_b64, sig_b64 = token.split(".")
    except ValueError:
        return None
    signing_input = f"{header_b64}.{payload_b64}".encode()
    expected_sig = hmac.new(SHOPIFY_CLIENT_SECRET.encode(), signing_input, hashlib.sha256).digest()
    try:
        actual_sig = _b64url_decode(sig_b64)
        payload = json.loads(_b64url_decode(payload_b64))
    except Exception:
        return None
    if not hmac.compare_digest(expected_sig, actual_sig):
        return None
    now = time.time()
    if payload.get("aud") != SHOPIFY_CLIENT_ID:
        return None
    if payload.get("exp", 0) < now or payload.get("nbf", now) > now:
        return None
    iss_host = urllib.parse.urlparse(payload.get("iss") or "").hostname
    dest_host = urllib.parse.urlparse(payload.get("dest") or "").hostname
    if not iss_host or iss_host != dest_host:
        return None
    return payload


@app.route("/app", methods=["GET"])
def embedded_app():
    """The page Shopify Admin iframes in when you click the app in your
    sidebar. Can't do the usual server-side auth check here -- App Bridge
    itself has to load first before it can mint a session token -- so
    this just serves a thin shell that calls shopify.idToken() client-side
    and fetches the real content from /app/data once it has one."""
    if not SHOPIFY_CLIENT_ID:
        return jsonify({"error": "SHOPIFY_CLIENT_ID not configured on this server"}), 500
    html = f"""<!doctype html><html><head><meta charset="utf-8">
<meta name="shopify-api-key" content="{SHOPIFY_CLIENT_ID}">
<title>920D Sync Status</title>
<script src="https://cdn.shopify.com/shopifycloud/app-bridge.js"></script>
<style>{DASHBOARD_CSS}</style></head><body>
<h1>920D Shopify &harr; Odoo Sync Status</h1>
<div id="content">Loading...</div>
<script>{FILTER_JS}
async function load(days) {{
  document.getElementById('content').innerHTML = 'Loading...';
  const token = await shopify.idToken();
  const resp = await fetch('/app/data?days=' + (days || 60), {{ headers: {{ 'Authorization': 'Bearer ' + token }} }});
  document.getElementById('content').innerHTML = await resp.text();
  const form = document.querySelector('#content form');
  if (form) {{
    form.addEventListener('submit', function(e) {{
      e.preventDefault();
      load(form.querySelector('input[name=days]').value);
    }});
  }}
  wireFilters();
}}
load();
</script>
</body></html>"""
    resp = Response(html, mimetype="text/html")
    resp.headers["Content-Security-Policy"] = (
        f"frame-ancestors https://{SHOPIFY_STORE_DOMAIN} https://admin.shopify.com;"
    )
    return resp


@app.route("/app/data", methods=["GET"])
def app_data():
    auth_header = request.headers.get("Authorization", "")
    token = auth_header[7:] if auth_header.startswith("Bearer ") else ""
    payload = verify_shopify_id_token(token) if token else None
    if not payload:
        return Response("Invalid session token", 401, {"X-Shopify-Retry-Invalid-Session-Request": "1"})
    if not (SHOPIFY_STORE_DOMAIN and SHOPIFY_CLIENT_ID and SHOPIFY_CLIENT_SECRET):
        return jsonify({"error": "Shopify API credentials not configured on this server"}), 500
    days = min(int(request.args.get("days", 60)), 365)
    try:
        rows = audit_sync(days)
    except urllib.error.HTTPError as e:
        return jsonify({"error": f"Shopify API error: {e.code} {e.read().decode()[:500]}"}), 502
    return Response(render_table_section(rows, days), mimetype="text/html")


@app.route("/healthz", methods=["GET"])
def healthz():
    return jsonify({"status": "ok"}), 200


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
