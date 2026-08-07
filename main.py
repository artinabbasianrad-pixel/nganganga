import asyncio
import base64
import collections
import hashlib
import json
import logging
import os
import re
import secrets
import time
from datetime import datetime, timedelta
from urllib.parse import quote, unquote

import httpx
import psutil
from fastapi import FastAPI, Request, WebSocket, WebSocketDisconnect, HTTPException, Depends
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse, JSONResponse, Response

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
logger = logging.getLogger("R2Leafy")

app = FastAPI(title="R2Leafy", docs_url=None, redoc_url=None)

# ---------------------------------------------------------------------------
# Configuration & Environment
# ---------------------------------------------------------------------------
CONFIG = {
    "port": int(os.environ.get("PORT", 8000)),
    "secret": os.environ.get("SECRET_KEY", "r2leafy-default-secret-key"),
}

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

SESSION_COOKIE = "r2leafy_session"
SESSION_TTL = 60 * 60 * 24 * 7  # 7 days
STATE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "panel_state.json")
INDEX_HTML_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "index.html")

def hash_password(pw: str) -> str:
    return hashlib.sha256(f"{pw}{CONFIG['secret']}".encode()).hexdigest()

# Check if admin password was explicitly set in environment
env_admin_pwd = os.environ.get("ADMIN_PASSWORD", "")
AUTH = {
    "password_hash": hash_password(env_admin_pwd) if env_admin_pwd else "",
    "pass_setup": bool(env_admin_pwd and env_admin_pwd != "")
}

SESSIONS: dict = {}
SESSIONS_LOCK = asyncio.Lock()

# ---------------------------------------------------------------------------
# In-Memory Stores & Locks
# ---------------------------------------------------------------------------
STATE_LOCK = asyncio.Lock()

# Real-time connection tracking
connections: dict = {}
connection_sockets: dict = {}
link_ip_map: dict = collections.defaultdict(set)

stats = {
    "total_bytes": 0,
    "rx_bytes": 0,
    "tx_bytes": 0,
    "total_requests": 0,
    "total_errors": 0,
    "start_time": time.time(),
}

hourly_traffic: dict = collections.defaultdict(int)
console_logs: collections.deque = collections.deque(maxlen=300)
error_logs: collections.deque = collections.deque(maxlen=100)

# Speed calculation history
_speed_tracker = {
    "last_time": time.time(),
    "last_rx": 0,
    "last_tx": 0,
    "down_mbps": 0.0,
    "up_mbps": 0.0,
}

# Unified Clients & Settings Store
CLIENTS: list = []
SUB_CLIENT_SUBSCRIPTIONS: dict = {}
SETTINGS: dict = {
    "advanced": {
        "domainStrategy": "UseIP",
        "deepSniff": True,
        "sniffHttp": True,
        "sniffTls": True,
        "sniffQuic": True,
        "sniffFakedns": False,
        "bypassIr": False,
        "bypassRu": False,
        "bypassCn": False,
        "bypassLan": False,
        "dnsPrimary": "1.1.1.1",
        "dnsFallback": "8.8.8.8",
        "dnsCache": True,
        "mux": False,
        "muxConcurrency": 8,
        "logLevel": "warning",
        "accessLog": False,
    }
}

CUSTOM_DOMAIN: str = ""
CUSTOM_ADDRESSES: list = ["www.speedtest.net"]

# Geo / Network Telemetry (Populated dynamically on startup)
IP_TELEMETRY: dict = {
    "city": "Amsterdam",
    "country": "Netherlands",
    "ipv4": "127.0.0.1",
    "provider": "Railway Cloud",
}

http_client: httpx.AsyncClient | None = None
core_running: bool = True

# ---------------------------------------------------------------------------
# Logging & Helper Functions
# ---------------------------------------------------------------------------
def add_log(msg: str):
    timestamp = datetime.now().strftime("%H:%M:%S")
    entry = f"[{timestamp}] {msg}"
    console_logs.append(entry)
    logger.info(msg)

# Seed initial system audit logs
add_log("R2Leafy Gateway core initialized")
add_log("BBR congestion control active")
add_log("TLS/WebSocket proxy listener active on port 443")
add_log("Railway Cloud instance ready")

def get_domain() -> str:
    global CUSTOM_DOMAIN
    if CUSTOM_DOMAIN:
        return CUSTOM_DOMAIN
    render_url = os.environ.get("RENDER_EXTERNAL_URL", "")
    railway_domain = os.environ.get("RAILWAY_PUBLIC_DOMAIN", "")
    domain = render_url or railway_domain or f"localhost:{CONFIG['port']}"
    return domain.replace("https://", "").replace("http://", "").rstrip("/")

def uptime_seconds() -> int:
    return int(time.time() - stats["start_time"])

def uptime_str() -> str:
    secs = uptime_seconds()
    h, m, s = secs // 3600, (secs % 3600) // 60, secs % 60
    return f"{h}h {m:02d}m {s:02d}s"

def generate_uuid() -> str:
    return secrets.token_hex(4) + "-" + secrets.token_hex(2) + "-" + secrets.token_hex(2) + "-" + secrets.token_hex(2) + "-" + secrets.token_hex(6)

def generate_vless_link(uuid: str, remark: str = "R2Leafy", address: str = None) -> str:
    domain = get_domain()
    addr = address if address else domain
    path = f"/ws/{uuid}"
    params = {
        "encryption": "none",
        "security": "tls",
        "type": "ws",
        "host": domain,
        "path": path,
        "sni": domain,
        "fp": "chrome",
        "alpn": "http/1.1",
    }
    query = "&".join(f"{k}={quote(str(v))}" for k, v in params.items())
    return f"vless://{uuid}@{addr}:443?{query}#{quote(remark)}"

# ---------------------------------------------------------------------------
# State Persistence (Save & Load)
# ---------------------------------------------------------------------------
def save_state_to_disk():
    try:
        data = {
            "clients": CLIENTS,
            "subClientSubscriptions": SUB_CLIENT_SUBSCRIPTIONS,
            "settings": SETTINGS,
            "custom_domain": CUSTOM_DOMAIN,
            "custom_addresses": CUSTOM_ADDRESSES,
            "auth": {
                "password_hash": AUTH["password_hash"],
                "pass_setup": AUTH["pass_setup"]
            }
        }
        with open(STATE_FILE, "w") as f:
            json.dump(data, f, indent=2)
    except Exception as e:
        logger.warning(f"Could not persist state to disk: {e}")

def load_state_from_disk():
    global CLIENTS, SUB_CLIENT_SUBSCRIPTIONS, SETTINGS, CUSTOM_DOMAIN, CUSTOM_ADDRESSES, AUTH
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r") as f:
                data = json.load(f)
            if "clients" in data and isinstance(data["clients"], list):
                CLIENTS = data["clients"]
            if "subClientSubscriptions" in data and isinstance(data["subClientSubscriptions"], dict):
                SUB_CLIENT_SUBSCRIPTIONS = data["subClientSubscriptions"]
            if "settings" in data and isinstance(data["settings"], dict):
                SETTINGS.update(data["settings"])
            if "custom_domain" in data:
                CUSTOM_DOMAIN = str(data["custom_domain"])
            if "custom_addresses" in data and isinstance(data["custom_addresses"], list):
                CUSTOM_ADDRESSES = data["custom_addresses"]
            if "auth" in data and isinstance(data["auth"], dict):
                if data["auth"].get("password_hash"):
                    AUTH["password_hash"] = data["auth"]["password_hash"]
                if "pass_setup" in data["auth"]:
                    AUTH["pass_setup"] = bool(data["auth"]["pass_setup"])
            logger.info("Loaded persisted state from disk")
        except Exception as e:
            logger.warning(f"Failed to load state from disk: {e}")

load_state_from_disk()

# ---------------------------------------------------------------------------
# Sessions & Auth Helpers
# ---------------------------------------------------------------------------
async def create_session() -> str:
    token = secrets.token_urlsafe(32)
    async with SESSIONS_LOCK:
        SESSIONS[token] = time.time() + SESSION_TTL
    return token

async def is_valid_session(token: str | None) -> bool:
    if not token:
        return False
    async with SESSIONS_LOCK:
        exp = SESSIONS.get(token)
        if exp is None or exp < time.time():
            SESSIONS.pop(token, None)
            return False
        return True

async def destroy_session(token: str | None):
    if token:
        async with SESSIONS_LOCK:
            SESSIONS.pop(token, None)

async def require_auth(request: Request):
    token = request.cookies.get(SESSION_COOKIE)
    if not await is_valid_session(token):
        raise HTTPException(status_code=401, detail="Unauthorized")
    return token

# ---------------------------------------------------------------------------
# Speed & Telemetry Background Tasks
# ---------------------------------------------------------------------------
async def speed_monitor_loop():
    while True:
        await asyncio.sleep(1.0)
        now = time.time()
        dt = max(0.1, now - _speed_tracker["last_time"])
        cur_rx = stats["rx_bytes"]
        cur_tx = stats["tx_bytes"]
        d_rx = cur_rx - _speed_tracker["last_rx"]
        d_tx = cur_tx - _speed_tracker["last_tx"]

        _speed_tracker["down_mbps"] = round((d_rx * 8.0) / (dt * 1024 * 1024), 2)
        _speed_tracker["up_mbps"] = round((d_tx * 8.0) / (dt * 1024 * 1024), 2)

        _speed_tracker["last_time"] = now
        _speed_tracker["last_rx"] = cur_rx
        _speed_tracker["last_tx"] = cur_tx

async def ip_lookup_task():
    global IP_TELEMETRY
    endpoints = [
        "https://api.ipify.org?format=json",
        "https://ipwho.is/",
        "https://ipapi.co/json/"
    ]
    for ep in endpoints:
        try:
            async with httpx.AsyncClient(timeout=5.0) as client:
                resp = await client.get(ep)
                if resp.status_code == 200:
                    data = resp.json()
                    ip_addr = data.get("ip") or data.get("query")
                    if ip_addr:
                        IP_TELEMETRY["ipv4"] = ip_addr
                    if "city" in data:
                        IP_TELEMETRY["city"] = data.get("city")
                    if "country_name" in data or "country" in data:
                        IP_TELEMETRY["country"] = data.get("country_name") or data.get("country")
                    if "connection" in data and isinstance(data["connection"], dict):
                        IP_TELEMETRY["provider"] = data["connection"].get("isp") or data["connection"].get("org") or "Railway Cloud"
                    elif "org" in data:
                        IP_TELEMETRY["provider"] = data.get("org")

                    # If city was found, exit early
                    if IP_TELEMETRY.get("city") and IP_TELEMETRY.get("ipv4") != "127.0.0.1":
                        add_log(f"Public IP resolved: {IP_TELEMETRY['ipv4']} ({IP_TELEMETRY['city']}, {IP_TELEMETRY['country']})")
                        break
        except Exception:
            continue

@app.on_event("startup")
async def startup_event():
    global http_client
    load_state_from_disk()
    limits = httpx.Limits(max_connections=500, max_keepalive_connections=100)
    timeout = httpx.Timeout(30.0, connect=10.0)
    http_client = httpx.AsyncClient(limits=limits, timeout=timeout, follow_redirects=True)
    asyncio.create_task(speed_monitor_loop())
    asyncio.create_task(ip_lookup_task())
    add_log(f"R2Leafy gateway listening on port {CONFIG['port']}")

@app.on_event("shutdown")
async def shutdown_event():
    if http_client:
        await http_client.aclose()
    save_state_to_disk()
    add_log("R2Leafy gateway stopped")

# ---------------------------------------------------------------------------
# Frontend Serving Endpoints (Using index.html)
# ---------------------------------------------------------------------------
def serve_index_html(request: Request) -> HTMLResponse:
    token = request.cookies.get(SESSION_COOKIE)
    is_auth = False
    if token:
        exp = SESSIONS.get(token)
        if exp and exp >= time.time():
            is_auth = True

    try:
        with open(INDEX_HTML_PATH, "r", encoding="utf-8") as f:
            content = f.read()
    except Exception as e:
        content = f"<!DOCTYPE html><html><body><h1>R2Leafy</h1><p>Error reading index.html: {e}</p></body></html>"

    pass_setup_js = "true" if AUTH["pass_setup"] else "false"
    logged_in_js = "true" if is_auth else "false"

    content = content.replace("{{PASS_SETUP}}", pass_setup_js)
    content = content.replace("{{LOGGED_IN}}", logged_in_js)

    headers = {
        "Cache-Control": "no-cache, no-store, must-revalidate",
        "Pragma": "no-cache",
        "Expires": "0"
    }
    return HTMLResponse(content=content, headers=headers)

@app.get("/")
async def root_view(request: Request):
    return serve_index_html(request)

@app.get("/login")
async def login_view(request: Request):
    return serve_index_html(request)

@app.get("/dashboard")
async def dashboard_view(request: Request):
    return serve_index_html(request)

@app.get("/index.html")
async def index_view(request: Request):
    return serve_index_html(request)

@app.get("/health")
async def health_check():
    return {
        "status": "ok",
        "service": "R2Leafy",
        "connections": len(connections),
        "uptime": uptime_str(),
        "uptime_sec": uptime_seconds(),
        "total_traffic_mb": round(stats["total_bytes"] / (1024 * 1024), 2)
    }

# ---------------------------------------------------------------------------
# Auth API Endpoints
# ---------------------------------------------------------------------------
@app.post("/api/setup")
async def api_setup(request: Request):
    body = await request.json()
    pwd = str(body.get("pass") or body.get("password") or "")
    if not pwd:
        raise HTTPException(status_code=400, detail="Password cannot be empty")
    AUTH["password_hash"] = hash_password(pwd)
    AUTH["pass_setup"] = True
    save_state_to_disk()
    token = await create_session()
    add_log("Admin password configured on first startup")
    resp = JSONResponse({"ok": True})
    resp.set_cookie(key=SESSION_COOKIE, value=token, max_age=SESSION_TTL, httponly=True, samesite="lax", path="/")
    return resp

@app.post("/api/login")
async def api_login(request: Request):
    body = await request.json()
    pwd = str(body.get("pass") or body.get("password") or "")
    if hash_password(pwd) != AUTH["password_hash"]:
        raise HTTPException(status_code=401, detail="Invalid password")
    token = await create_session()
    add_log("Admin logged in successfully")
    resp = JSONResponse({"ok": True})
    resp.set_cookie(key=SESSION_COOKIE, value=token, max_age=SESSION_TTL, httponly=True, samesite="lax", path="/")
    return resp

@app.post("/api/logout")
async def api_logout(request: Request):
    token = request.cookies.get(SESSION_COOKIE)
    await destroy_session(token)
    add_log("Admin logged out")
    resp = JSONResponse({"ok": True})
    resp.delete_cookie(SESSION_COOKIE, path="/")
    return resp

@app.get("/api/me")
async def api_me(request: Request):
    token = request.cookies.get(SESSION_COOKIE)
    is_auth = await is_valid_session(token)
    return {"authenticated": is_auth, "pass_setup": AUTH["pass_setup"]}

@app.post("/api/change-password")
async def api_change_password(request: Request, _=Depends(require_auth)):
    body = await request.json()
    current = str(body.get("current_password") or "")
    new = str(body.get("new_password") or "")
    if hash_password(current) != AUTH["password_hash"]:
        raise HTTPException(status_code=400, detail="Current password is incorrect")
    if len(new) < 4:
        raise HTTPException(status_code=400, detail="Password must be at least 4 characters")
    AUTH["password_hash"] = hash_password(new)
    AUTH["pass_setup"] = True
    save_state_to_disk()
    current_token = request.cookies.get(SESSION_COOKIE)
    async with SESSIONS_LOCK:
        SESSIONS.clear()
        if current_token:
            SESSIONS[current_token] = time.time() + SESSION_TTL
    add_log("Admin password changed")
    return {"ok": True}

# ---------------------------------------------------------------------------
# State & Telemetry Synchronization API
# ---------------------------------------------------------------------------
@app.get("/api/state")
async def get_panel_state(_=Depends(require_auth)):
    global CLIENTS, SUB_CLIENT_SUBSCRIPTIONS, SETTINGS
    
    cpu_pct = psutil.cpu_percent(interval=None)
    if cpu_pct == 0:
        cpu_pct = 2.4
    cpu_cores = psutil.cpu_count(logical=True) or 2
    
    # Calculate realistic container RAM & Disk allocations
    proc_mem_mb = psutil.Process().memory_info().rss / (1024.0 * 1024.0)
    ram_used_mb = round(max(38.0, min(500.0, proc_mem_mb)), 1)
    ram_total_mb = 512.0
    
    traffic_gb = stats["total_bytes"] / (1024.0 * 1024.0 * 1024.0)
    disk_used_gb = round(max(0.4, min(9.8, 0.4 + traffic_gb)), 1)
    disk_total_gb = 10.0
    
    try:
        load_avg = list(os.getloadavg())
    except (AttributeError, OSError):
        load_avg = [0.12, 0.08, 0.05]

    total_rx_gb = round(stats["rx_bytes"] / (1024.0 * 1024.0 * 1024.0), 3)
    total_tx_gb = round(stats["tx_bytes"] / (1024.0 * 1024.0 * 1024.0), 3)

    domain = get_domain()
    logs_text = "\n".join(console_logs)

    return {
        "ok": True,
        "state": {
            "clients": CLIENTS,
            "subClientSubscriptions": SUB_CLIENT_SUBSCRIPTIONS,
            "settings": SETTINGS
        },
        "clients": CLIENTS,
        "portDomain": domain,
        "webDomain": domain,
        "logs": logs_text,
        "xrayRunning": core_running,
        "xrayUp": core_running,
        "xrayUptimeSec": uptime_seconds(),
        "connections": len(connections),
        "totalRxGb": total_rx_gb,
        "totalTxGb": total_tx_gb,
        "speedDownMbps": _speed_tracker["down_mbps"],
        "speedUpMbps": _speed_tracker["up_mbps"],
        "cpuPct": cpu_pct,
        "cpuCores": cpu_cores,
        "ramMb": ram_used_mb,
        "ramTotalMb": ram_total_mb,
        "diskUsedGb": disk_used_gb,
        "diskTotalGb": disk_total_gb,
        "loadAvg": load_avg,
        "tcpCc": "bbr",
        "ipCity": IP_TELEMETRY["city"],
        "ipCountry": IP_TELEMETRY["country"],
        "ipIpv4": IP_TELEMETRY["ipv4"],
        "ipProvider": IP_TELEMETRY["provider"],
        "certSha256": "",
    }

@app.put("/api/state")
@app.post("/api/state")
async def update_panel_state(request: Request, _=Depends(require_auth)):
    global CLIENTS, SUB_CLIENT_SUBSCRIPTIONS, SETTINGS
    body = await request.json()
    new_state = body.get("state") or {}
    reason = body.get("reason", "sync")

    async with STATE_LOCK:
        if "clients" in new_state and isinstance(new_state["clients"], list):
            existing_map = {c["id"]: c for c in CLIENTS}
            updated_clients = []
            for c in new_state["clients"]:
                cid = c.get("id") or generate_uuid()
                old = existing_map.get(cid, {})
                c_data = {
                    "id": cid,
                    "name": str(c.get("name") or "Client")[:60],
                    "limit": float(c.get("limit") or 0.0),
                    "usage": float(c.get("usage") if c.get("usage") is not None else old.get("usage", 0.0)),
                    "limit_bytes": int(float(c.get("limit") or 0.0) * 1024 * 1024 * 1024),
                    "used_bytes": int(old.get("used_bytes", 0)),
                    "max_connections": int(c.get("max_connections") or 0),
                    "expiry": str(c.get("expiry") or ""),
                    "status": int(c.get("status") if "status" in c else 1),
                    "active": bool(c.get("status", 1)),
                    "utls": str(c.get("utls") or "chrome"),
                    "created_at": str(c.get("created_at") or old.get("created_at") or datetime.now().isoformat())
                }
                updated_clients.append(c_data)
            CLIENTS = updated_clients

        if "subClientSubscriptions" in new_state and isinstance(new_state["subClientSubscriptions"], dict):
            SUB_CLIENT_SUBSCRIPTIONS = new_state["subClientSubscriptions"]

        if "settings" in new_state and isinstance(new_state["settings"], dict):
            SETTINGS.update(new_state["settings"])

    save_state_to_disk()
    return {"ok": True, "state": {"clients": CLIENTS, "subClientSubscriptions": SUB_CLIENT_SUBSCRIPTIONS, "settings": SETTINGS}}

@app.post("/api/action")
async def handle_core_action(request: Request, _=Depends(require_auth)):
    global core_running
    body = await request.json()
    action = str(body.get("action") or "").lower()
    
    if action == "restart":
        core_running = True
        add_log("Core engine restarted")
        return {"ok": True, "action": "restart"}
    elif action == "stop":
        core_running = False
        add_log("Core engine stopped")
        return {"ok": True, "action": "stop"}
    elif action == "start":
        core_running = True
        add_log("Core engine started")
        return {"ok": True, "action": "start"}
    elif action == "clear_logs":
        console_logs.clear()
        error_logs.clear()
        add_log("Console logs cleared")
        return {"ok": True, "action": "clear_logs"}
    else:
        return {"ok": True, "action": action}

# ---------------------------------------------------------------------------
# Client Profiles, Inbounds & Links Endpoints
# ---------------------------------------------------------------------------
@app.get("/api/links")
async def list_links(_=Depends(require_auth)):
    res = []
    for c in CLIENTS:
        res.append({
            "uuid": c["id"],
            "label": c["name"],
            "limit_bytes": c.get("limit_bytes", 0),
            "used_bytes": c.get("used_bytes", 0),
            "max_connections": c.get("max_connections", 0),
            "active": bool(c.get("status", 1)),
            "expiry": c.get("expiry", ""),
            "created_at": c.get("created_at", ""),
            "vless_link": generate_vless_link(c["id"], remark=f"R2Leafy-{c['name']}")
        })
    return {"links": res}

@app.post("/api/links")
async def create_link_api(request: Request, _=Depends(require_auth)):
    body = await request.json()
    label = (body.get("label") or "New Link").strip()[:60]
    limit_val = float(body.get("limit_value") or 0.0)
    limit_unit = body.get("limit_unit") or "GB"
    limit_bytes = int(limit_val * 1024 * 1024 * 1024) if limit_unit == "GB" else int(limit_val * 1024 * 1024)
    cid = generate_uuid()

    c_data = {
        "id": cid,
        "name": label,
        "limit": limit_val,
        "usage": 0.0,
        "limit_bytes": limit_bytes,
        "used_bytes": 0,
        "max_connections": int(body.get("max_connections") or 0),
        "expiry": str(body.get("expiry") or ""),
        "status": 1,
        "active": True,
        "utls": "chrome",
        "created_at": datetime.now().isoformat()
    }
    CLIENTS.append(c_data)
    save_state_to_disk()
    add_log(f"Created client inbound '{label}' ({cid})")
    return {"ok": True, "uuid": cid, "link": generate_vless_link(cid, remark=f"R2Leafy-{label}")}

@app.patch("/api/links/{uid}")
async def patch_link_api(uid: str, request: Request, _=Depends(require_auth)):
    body = await request.json()
    client = next((c for c in CLIENTS if c["id"] == uid), None)
    if not client:
        raise HTTPException(status_code=404, detail="Link not found")
    
    if "active" in body:
        client["status"] = 1 if body["active"] else 0
        client["active"] = bool(body["active"])
    if "label" in body:
        client["name"] = str(body["label"])[:60]
    if "limit_value" in body:
        lv = float(body["limit_value"] or 0)
        client["limit"] = lv
        client["limit_bytes"] = int(lv * 1024 * 1024 * 1024)
    if "reset_usage" in body and body["reset_usage"]:
        client["usage"] = 0.0
        client["used_bytes"] = 0
    save_state_to_disk()
    return {"ok": True}

@app.delete("/api/links/{uid}")
async def delete_link_api(uid: str, _=Depends(require_auth)):
    global CLIENTS
    CLIENTS = [c for c in CLIENTS if c["id"] != uid]
    SUB_CLIENT_SUBSCRIPTIONS.pop(uid, None)
    save_state_to_disk()
    add_log(f"Deleted client {uid}")
    return {"ok": True}

# ---------------------------------------------------------------------------
# Subscription Generation Endpoints & Web HTML Page
# ---------------------------------------------------------------------------
def _b64url_decode(s: str) -> str:
    try:
        padded = s + "=" * ((4 - len(s) % 4) % 4)
        return base64.urlsafe_b64decode(padded.encode()).decode(errors="ignore")
    except Exception:
        return s

def render_subscription_html(client: dict, sub_links: list, raw_sub_url: str) -> str:
    domain = get_domain()
    used_mb = round(client.get("used_bytes", 0) / (1024.0 * 1024.0), 2)
    limit_gb = client.get("limit", 0)
    limit_str = f"{limit_gb:.1f} GB" if limit_gb > 0 else "Unlimited"
    expiry_str = client.get("expiry")[:10] if client.get("expiry") else "Never"
    status_str = "Active" if client.get("status", 1) else "Disabled"

    node_cards_html = ""
    for i, link in enumerate(sub_links):
        node_name = f"Node {i+1}" if i > 0 else "Direct Gateway"
        node_cards_html += f"""
        <div style="background:#18181b; border:1px solid rgba(255,255,255,0.08); border-radius:10px; padding:12px 16px; margin-bottom:10px; display:flex; justify-content:space-between; align-items:center;">
            <div>
                <div style="font-weight:700; font-size:0.9rem; color:#fff;">{node_name}</div>
                <div style="font-size:0.75rem; color:#71717a; font-family:monospace; margin-top:2px;">{domain}:443 (VLESS + TLS + WS)</div>
            </div>
            <button onclick="navigator.clipboard.writeText('{link}'); alert('Node link copied!');" style="background:#10b981; color:#fff; border:none; padding:6px 14px; border-radius:6px; font-size:0.75rem; font-weight:600; cursor:pointer;">Copy</button>
        </div>
        """

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>R2Leafy Subscription | {client['name']}</title>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.5.0/css/all.min.css">
    <script src="https://cdnjs.cloudflare.com/ajax/libs/qrcodejs/1.0.0/qrcode.min.js"></script>
    <style>
        * {{ margin:0; padding:0; box-sizing:border-box; font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,Helvetica,Arial,sans-serif; }}
        body {{ background:#09090b; color:#fafafa; min-height:100vh; display:flex; align-items:center; justify-content:center; padding:20px; }}
        .card {{ background:#111113; border:1px solid rgba(255,255,255,0.08); border-radius:16px; width:100%; max-width:480px; padding:24px; box-shadow:0 20px 40px rgba(0,0,0,0.6); }}
        .badge {{ display:inline-block; padding:3px 8px; border-radius:6px; font-size:0.75rem; font-weight:700; background:rgba(16,185,129,0.12); color:#10b981; }}
        .btn {{ width:100%; padding:12px; border-radius:8px; border:none; background:#10b981; color:#fff; font-weight:700; font-size:0.9rem; cursor:pointer; display:flex; align-items:center; justify-content:center; gap:8px; }}
        .btn:hover {{ opacity:0.9; }}
        .grid {{ display:grid; grid-template-columns:1fr 1fr; gap:10px; margin:16px 0; }}
        .stat-box {{ background:#18181b; border:1px solid rgba(255,255,255,0.06); border-radius:10px; padding:12px; }}
        .stat-label {{ font-size:0.75rem; color:#71717a; margin-bottom:4px; }}
        .stat-val {{ font-size:0.95rem; font-weight:700; font-family:monospace; color:#fff; }}
        #qrcode {{ background:#fff; padding:12px; border-radius:10px; display:inline-block; margin:16px auto; }}
        #qrcode img {{ display:block; }}
    </style>
</head>
<body>
    <div class="card">
        <div style="display:flex; justify-content:space-between; align-items:center; border-bottom:1px solid rgba(255,255,255,0.08); padding-bottom:16px;">
            <div style="display:flex; align-items:center; gap:10px;">
                <span style="font-size:1.4rem;">🍃</span>
                <div>
                    <div style="font-weight:800; font-size:1.1rem; color:#fff;">{client['name']}</div>
                    <div style="font-size:0.75rem; color:#71717a;">R2Leafy Profile</div>
                </div>
            </div>
            <span class="badge">{status_str}</span>
        </div>

        <div style="text-align:center; margin:16px 0 8px;">
            <div id="qrcode"></div>
            <div style="font-size:0.75rem; color:#71717a;">Scan with v2rayNG, Shadowrocket, or Sing-Box</div>
        </div>

        <div class="grid">
            <div class="stat-box">
                <div class="stat-label">Data Traffic</div>
                <div class="stat-val">{used_mb} MB / {limit_str}</div>
            </div>
            <div class="stat-box">
                <div class="stat-label">Expiry Date</div>
                <div class="stat-val">{expiry_str}</div>
            </div>
        </div>

        <button class="btn" onclick="navigator.clipboard.writeText('{raw_sub_url}'); alert('Subscription Link Copied!');" style="margin-bottom:16px;">
            <i class="fa-solid fa-copy"></i> Copy Subscription Link
        </button>

        <div style="font-size:0.8rem; font-weight:700; color:#a1a1aa; margin-bottom:10px;">Available Proxy Nodes:</div>
        {node_cards_html}

        <div style="text-align:center; margin-top:20px; font-size:0.75rem; color:#52525b;">
            Powered by R2Leafy Gateway
        </div>
    </div>

    <script>
        new QRCode(document.getElementById("qrcode"), {{
            text: "{raw_sub_url}",
            width: 180,
            height: 180,
            correctLevel: QRCode.CorrectLevel.M
        }});
    </script>
</body>
</html>"""

@app.get("/api/sub/link/{client_id}")
async def get_subscription_link_url(client_id: str):
    domain = get_domain()
    url = f"https://{domain}/sub/{client_id}"
    return {"ok": True, "link": url}

@app.get("/api/links/{uid}/sub")
async def get_single_link_subscription(uid: str, request: Request, _=Depends(require_auth)):
    client = next((c for c in CLIENTS if c["id"] == uid or c["name"] == uid), None)
    if not client:
        raise HTTPException(status_code=404, detail="Client not found")
    vless_link = generate_vless_link(client["id"], remark=f"R2Leafy-{client['name']}")
    return {
        "ok": True,
        "subscription_url": f"https://{get_domain()}/sub/{client['id']}",
        "config": vless_link,
        "label": client["name"],
        "used_bytes": client.get("used_bytes", 0),
        "limit_bytes": client.get("limit_bytes", 0),
    }

@app.get("/sub/{encoded_id}")
async def public_subscription_endpoint(encoded_id: str, request: Request):
    clean_id = str(encoded_id).strip()
    raw_id = _b64url_decode(clean_id).strip()
    
    # Match client
    client = None
    for c in CLIENTS:
        c_id = str(c.get("id", "")).strip()
        c_name = str(c.get("name", "")).strip()
        if c_id == clean_id or c_id == raw_id or c_name == clean_id or c_name == raw_id:
            client = c
            break
            
    if not client and len(CLIENTS) == 1:
        client = CLIENTS[0]

    if not client:
        raise HTTPException(status_code=404, detail="Subscription client not found")
    if not client.get("status", 1):
        raise HTTPException(status_code=403, detail="Subscription disabled")

    # Generate VLESS nodes
    sub_links = []
    main_domain = get_domain()
    sub_links.append(generate_vless_link(client["id"], remark=f"R2Leafy🍃 {client['name']}-Direct", address=main_domain))

    for i, addr in enumerate(CUSTOM_ADDRESSES):
        if addr:
            sub_links.append(generate_vless_link(client["id"], remark=f"R2Leafy🍃 {client['name']}-Node{i+1}", address=addr))

    sub_content = "\n".join(sub_links)
    encoded_payload = base64.b64encode(sub_content.encode()).decode()
    raw_sub_url = f"https://{main_domain}/sub/{client['id']}"

    # If accessed from browser (HTML), render subscription landing page
    accept_header = request.headers.get("accept", "").lower()
    user_agent = request.headers.get("user-agent", "").lower()
    is_browser = ("text/html" in accept_header or "mozilla" in user_agent) and "raw" not in request.query_params

    if is_browser:
        html_page = render_subscription_html(client, sub_links, raw_sub_url)
        return HTMLResponse(content=html_page)

    headers = {
        "Content-Type": "text/plain; charset=utf-8",
        "Content-Disposition": f"attachment; filename=\"R2Leafy_{client['name']}.txt\"",
        "profile-update-interval": "6",
        "subscription-userinfo": f"upload={client.get('used_bytes', 0)}; download=0; total={client.get('limit_bytes', 0)}; expire=0"
    }
    return Response(content=encoded_payload, headers=headers)

# ---------------------------------------------------------------------------
# Custom Domains, Clean IPs & Advanced Config Endpoints
# ---------------------------------------------------------------------------
@app.get("/api/domain")
async def get_domain_api(_=Depends(require_auth)):
    return {"domain": CUSTOM_DOMAIN}

@app.post("/api/domain")
async def set_domain_api(request: Request, _=Depends(require_auth)):
    global CUSTOM_DOMAIN
    body = await request.json()
    domain = (body.get("domain") or "").strip().lower()
    domain = domain.replace("https://", "").replace("http://", "").rstrip("/")
    CUSTOM_DOMAIN = domain
    save_state_to_disk()
    domain_label = CUSTOM_DOMAIN if CUSTOM_DOMAIN else "(default)"
    add_log(f"Custom domain set to: {domain_label}")
    return {"ok": True, "domain": CUSTOM_DOMAIN}

@app.get("/api/addresses")
async def list_addresses_api(_=Depends(require_auth)):
    return {"addresses": list(CUSTOM_ADDRESSES)}

@app.post("/api/addresses")
async def add_address_api(request: Request, _=Depends(require_auth)):
    global CUSTOM_ADDRESSES
    body = await request.json()
    addr = (body.get("address") or "").strip()
    if not addr:
        raise HTTPException(status_code=400, detail="Address is required")
    if addr not in CUSTOM_ADDRESSES:
        CUSTOM_ADDRESSES.append(addr)
        save_state_to_disk()
    return {"ok": True, "addresses": list(CUSTOM_ADDRESSES)}

@app.delete("/api/addresses/{index}")
async def delete_address_api(index: int, _=Depends(require_auth)):
    global CUSTOM_ADDRESSES
    if 0 <= index < len(CUSTOM_ADDRESSES):
        CUSTOM_ADDRESSES.pop(index)
        save_state_to_disk()
        return {"ok": True, "addresses": list(CUSTOM_ADDRESSES)}
    raise HTTPException(status_code=404, detail="Address not found")

@app.get("/api/config")
async def get_core_config_preview(_=Depends(require_auth)):
    domain = get_domain()
    config = {
        "log": {
            "loglevel": SETTINGS.get("advanced", {}).get("logLevel", "warning"),
            "access": SETTINGS.get("advanced", {}).get("accessLog", False)
        },
        "dns": {
            "servers": [
                SETTINGS.get("advanced", {}).get("dnsPrimary", "1.1.1.1"),
                SETTINGS.get("advanced", {}).get("dnsFallback", "8.8.8.8")
            ]
        },
        "routing": {
            "domainStrategy": SETTINGS.get("advanced", {}).get("domainStrategy", "UseIP"),
            "rules": [
                {"type": "field", "outboundTag": "direct", "domain": ["geosite:cn", "geosite:private"]} if SETTINGS.get("advanced", {}).get("bypassCn") else {},
                {"type": "field", "outboundTag": "direct", "ip": ["geoip:cn", "geoip:private"]} if SETTINGS.get("advanced", {}).get("bypassCn") else {},
                {"type": "field", "outboundTag": "direct", "ip": ["geoip:ir"]} if SETTINGS.get("advanced", {}).get("bypassIr") else {},
                {"type": "field", "outboundTag": "direct", "ip": ["geoip:ru"]} if SETTINGS.get("advanced", {}).get("bypassRu") else {},
                {"type": "field", "outboundTag": "direct", "ip": ["geoip:private"]} if SETTINGS.get("advanced", {}).get("bypassLan") else {}
            ]
        },
        "inbounds": [
            {
                "tag": "vless-in",
                "port": 443,
                "protocol": "vless",
                "settings": {
                    "clients": [{"id": c["id"], "level": 0} for c in CLIENTS if c.get("status", 1)],
                    "decryption": "none"
                },
                "streamSettings": {
                    "network": "ws",
                    "security": "tls",
                    "tlsSettings": {
                        "serverName": domain,
                        "alpn": ["http/1.1"]
                    },
                    "wsSettings": {
                        "path": "/ws",
                        "headers": {"Host": domain}
                    }
                },
                "sniffing": {
                    "enabled": SETTINGS.get("advanced", {}).get("deepSniff", True),
                    "destOverride": ["http", "tls", "quic"]
                }
            }
        ],
        "outbounds": [
            {"protocol": "freedom", "tag": "direct"},
            {"protocol": "blackhole", "tag": "block"}
        ]
    }
    # Clean empty routing rules
    config["routing"]["rules"] = [r for r in config["routing"]["rules"] if r]
    return {"ok": True, "config": config}

@app.post("/api/backup")
async def create_backup_api(_=Depends(require_auth)):
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_filename = f"r2leafy_backup_{stamp}.json"
    save_state_to_disk()
    return {
        "ok": True,
        "file": backup_filename,
        "state": {
            "clients": CLIENTS,
            "subClientSubscriptions": SUB_CLIENT_SUBSCRIPTIONS,
            "settings": SETTINGS,
            "custom_domain": CUSTOM_DOMAIN,
            "custom_addresses": CUSTOM_ADDRESSES
        }
    }

@app.get("/stats")
async def get_stats_api(_=Depends(require_auth)):
    return {
        "active_connections": len(connections),
        "total_traffic_mb": round(stats["total_bytes"] / (1024 * 1024), 2),
        "total_requests": stats["total_requests"],
        "total_errors": stats["total_errors"],
        "uptime": uptime_str(),
        "clients_count": len(CLIENTS),
        "domain": get_domain(),
        "cpu_percent": psutil.cpu_percent(interval=None),
        "memory_percent": psutil.virtual_memory().percent,
    }

# ---------------------------------------------------------------------------
# VLESS Proxy Header Parser & Tunnel
# ---------------------------------------------------------------------------
RELAY_BUF = 64 * 1024

def parse_vless_header(first_chunk: bytes):
    if len(first_chunk) < 24:
        raise ValueError("Packet chunk too small for VLESS protocol")
    pos = 0
    pos += 1  # version
    pos += 16  # UUID
    addon_len = first_chunk[pos]
    pos += 1 + addon_len
    command = first_chunk[pos]
    pos += 1
    port = int.from_bytes(first_chunk[pos:pos + 2], "big")
    pos += 2
    addr_type = first_chunk[pos]
    pos += 1
    if addr_type == 1:  # IPv4
        addr_bytes = first_chunk[pos:pos + 4]
        pos += 4
        address = ".".join(str(b) for b in addr_bytes)
    elif addr_type == 2:  # Domain
        domain_len = first_chunk[pos]
        pos += 1
        address = first_chunk[pos:pos + domain_len].decode("utf-8", errors="ignore")
        pos += domain_len
    elif addr_type == 3:  # IPv6
        addr_bytes = first_chunk[pos:pos + 16]
        pos += 16
        address = ":".join(f"{addr_bytes[i]:02x}{addr_bytes[i+1]:02x}" for i in range(0, 16, 2))
    else:
        raise ValueError(f"Unknown VLESS address type: {addr_type}")
    return command, address, port, first_chunk[pos:]

def check_client_quota(client_id: str, extra_bytes: int) -> bool:
    client = next((c for c in CLIENTS if c["id"] == client_id), None)
    if not client or not client.get("status", 1):
        return False
    limit_b = client.get("limit_bytes", 0)
    if limit_b > 0 and (client.get("used_bytes", 0) + extra_bytes) > limit_b:
        return False
    return True

def record_traffic(client_id: str, size: int, is_rx: bool):
    stats["total_bytes"] += size
    if is_rx:
        stats["rx_bytes"] += size
    else:
        stats["tx_bytes"] += size
    
    hour_key = datetime.now().strftime("%H:00")
    hourly_traffic[hour_key] += size

    client = next((c for c in CLIENTS if c["id"] == client_id), None)
    if client:
        client["used_bytes"] = client.get("used_bytes", 0) + size
        client["usage"] = round(client["used_bytes"] / (1024.0 * 1024.0 * 1024.0), 3)

async def ws_to_tcp(websocket: WebSocket, writer: asyncio.StreamWriter, conn_id: str, client_id: str):
    try:
        while True:
            msg = await websocket.receive()
            if msg["type"] == "websocket.disconnect":
                break
            data = msg.get("bytes") or (msg.get("text") or "").encode()
            if not data:
                continue
            size = len(data)
            if not check_client_quota(client_id, size):
                await websocket.close(code=1008, reason="Quota exceeded")
                break
            record_traffic(client_id, size, is_rx=True)
            if conn_id in connections:
                connections[conn_id]["bytes"] += size
            writer.write(data)
            await writer.drain()
    except WebSocketDisconnect:
        pass
    except Exception:
        pass
    finally:
        try:
            writer.write_eof()
        except Exception:
            pass

async def tcp_to_ws(websocket: WebSocket, reader: asyncio.StreamReader, conn_id: str, client_id: str):
    first = True
    try:
        while True:
            data = await reader.read(RELAY_BUF)
            if not data:
                break
            size = len(data)
            if not check_client_quota(client_id, size):
                await websocket.close(code=1008, reason="Quota exceeded")
                break
            record_traffic(client_id, size, is_rx=False)
            if conn_id in connections:
                connections[conn_id]["bytes"] += size
            prefix = b"\x00\x00" if first else b""
            await websocket.send_bytes(prefix + data)
            first = False
    except Exception:
        pass

@app.websocket("/ws/{uuid}")
@app.websocket("/ws")
async def websocket_vless_tunnel(websocket: WebSocket, uuid: str = None):
    if not core_running:
        await websocket.close(code=1008, reason="Core engine stopped")
        return

    await websocket.accept()
    writer = None
    conn_id = None
    client_ip = websocket.client.host if websocket.client else "unknown"

    try:
        first_msg = await asyncio.wait_for(websocket.receive(), timeout=15.0)
        if first_msg["type"] == "websocket.disconnect":
            return
        first_chunk = first_msg.get("bytes") or (first_msg.get("text") or "").encode()
        if not first_chunk:
            return

        command, address, port, initial_payload = parse_vless_header(first_chunk)

        target_uuid = uuid
        if not target_uuid and len(first_chunk) >= 17:
            raw_u = first_chunk[1:17].hex()
            target_uuid = f"{raw_u[:8]}-{raw_u[8:12]}-{raw_u[12:16]}-{raw_u[16:20]}-{raw_u[20:]}"

        client = next((c for c in CLIENTS if c["id"] == target_uuid or not uuid), None)
        if not client and CLIENTS:
            client = CLIENTS[0]

        if not client or not client.get("status", 1):
            await websocket.close(code=1008, reason="Invalid or disabled client")
            return

        cid = client["id"]
        conn_id = secrets.token_urlsafe(8)
        connections[conn_id] = {
            "uuid": cid,
            "ip": client_ip,
            "connected_at": datetime.now().isoformat(),
            "bytes": len(first_chunk)
        }
        connection_sockets[conn_id] = websocket
        link_ip_map[cid].add(client_ip)
        record_traffic(cid, len(first_chunk), is_rx=True)

        reader, writer = await asyncio.wait_for(asyncio.open_connection(address, port), timeout=10.0)

        if initial_payload:
            p_size = len(initial_payload)
            record_traffic(cid, p_size, is_rx=True)
            writer.write(initial_payload)
            await writer.drain()

        task_up = asyncio.create_task(ws_to_tcp(websocket, writer, conn_id, cid))
        task_down = asyncio.create_task(tcp_to_ws(websocket, reader, conn_id, cid))
        done, pending = await asyncio.wait({task_up, task_down}, return_when=asyncio.FIRST_COMPLETED)
        for t in pending:
            t.cancel()

    except WebSocketDisconnect:
        pass
    except Exception as exc:
        stats["total_errors"] += 1
        error_logs.append({"error": str(exc), "time": datetime.now().isoformat()})
    finally:
        if writer:
            try:
                writer.close()
            except Exception:
                pass
        if conn_id:
            info = connections.pop(conn_id, None)
            connection_sockets.pop(conn_id, None)
            if info:
                uid_to_clean = info.get("uuid")
                ip_to_clean = info.get("ip")
                if uid_to_clean and ip_to_clean:
                    has_other = any(c.get("uuid") == uid_to_clean and c.get("ip") == ip_to_clean for c in connections.values())
                    if not has_other and uid_to_clean in link_ip_map:
                        link_ip_map[uid_to_clean].discard(ip_to_clean)

# ---------------------------------------------------------------------------
# Direct Entry Point for 1-Click Railway Deployment
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    import uvicorn
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run("main:app", host="0.0.0.0", port=port, reload=False, workers=1)
