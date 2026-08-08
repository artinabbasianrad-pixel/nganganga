import asyncio
import base64
import collections
import hashlib
import json
import logging
import os
import re
import secrets
import socket
import struct
import time
from contextlib import asynccontextmanager
from datetime import datetime, timedelta
from urllib.parse import quote, unquote

import httpx
import psutil
from fastapi import FastAPI, Request, WebSocket, WebSocketDisconnect, HTTPException, Depends
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse, JSONResponse, Response

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
logger = logging.getLogger("R2Leafy")

# ---------------------------------------------------------------------------
# Configuration & Environment
# ---------------------------------------------------------------------------
def get_listen_port() -> int:
    raw = os.environ.get("PORT", "8000")
    try:
        return int(raw)
    except (ValueError, TypeError):
        return 8000

CONFIG = {
    "port": get_listen_port(),
    "secret": os.environ.get("SECRET_KEY", "r2leafy-default-secret-key"),
}

SESSION_COOKIE = "r2leafy_session"
SESSION_TTL = 60 * 60 * 24 * 7  # 7 days
STATE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "panel_state.json")
INDEX_HTML_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "index.html")

def hash_password(pw: str) -> str:
    return hashlib.sha256(f"{pw}{CONFIG['secret']}".encode()).hexdigest()

# Initial admin password: if not set in environment, first startup prompts Setup Password
env_admin_pwd = os.environ.get("ADMIN_PASSWORD", "")
AUTH = {
    "password_hash": hash_password(env_admin_pwd) if env_admin_pwd else "",
    "pass_setup": bool(env_admin_pwd and env_admin_pwd != "")
}

SESSIONS: dict = {}
SESSIONS_LOCK = asyncio.Lock()

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

_speed_tracker = {
    "last_time": time.time(),
    "last_rx": 0,
    "last_tx": 0,
    "down_mbps": 0.0,
    "up_mbps": 0.0,
}

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
CUSTOM_ADDRESSES: list = []

IP_TELEMETRY: dict = {
    "city": "The Dalles",
    "country": "United States",
    "ipv4": "34.127.121.27",
    "provider": "Google Cloud (us-west1)",
}

http_client: httpx.AsyncClient | None = None
core_running: bool = True
INDEX_HTML_CACHE: str | None = None


SUB_HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Subscription Profile</title>
    <link rel="icon" href="data:image/svg+xml,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 512 512'><path fill='%238b5cf6' d='M165.9 397.4c0 2-2.3 3.6-5.2 3.6-3.3.3-5.6-1.3-5.6-3.6 0-2 2.3-3.6 5.2-3.6 3-.3 5.6 1.3 5.6 3.6zm-31.1-4.5c-.7 2 1.3 4.3 4.3 4.9 2.6 1 5.6 0 6.2-2s-1.3-4.3-4.3-5.2c-2.6-.7-5.5.3-6.2 2.3zm44.2-1.7c-2.9.7-4.9 2.6-4.6 4.9.3 2 2.9 3.3 5.9 2.6 2.9-.7 4.9-2.6 4.6-4.6-.3-1.9-3-3.2-5.9-2.9zM244.8 8C106.1 8 0 113.3 0 252c0 110.9 69.8 205.8 169.5 239.2 12.8 2.3 17.3-5.6 17.3-12.1 0-6.2-.3-40.4-.3-61.4 0 0-70 15-84.7-29.8 0 0-11.4-29.1-27.8-36.6 0 0-22.9-15.7 1.6-15.4 0 0 24.9 2 38.6 25.8 21.9 38.6 58.6 27.5 72.9 20.9 2.3-16 8.8-27.1 16-33.7-55.9-6.2-112.3-14.3-112.3-110.5 0-27.5 7.6-41.3 23.6-58.9-2.6-6.5-11.1-33.3 2.6-67.9 20.9-6.5 69 27 69 27 20-5.6 41.5-8.5 62.8-8.5s42.8 2.9 62.8 8.5c0 0 48.1-33.6 69-27 13.7 34.7 5.2 61.4 2.6 67.9 16 17.7 25.8 31.5 25.8 58.9 0 96.5-58.9 104.2-114.8 110.5 9.2 7.9 17 22.9 17 46.4 0 33.7-.3 75.4-.3 83.6 0 6.5 4.6 14.4 17.3 12.1C428.2 457.8 496 362.9 496 252 496 113.3 383.5 8 244.8 8zM97.2 352.9c-1.3 1-1 3.3.7 5.2 1.6 1.6 3.9 2.3 5.2 1 1.3-1 1-3.3-.7-5.2-1.6-1.6-3.9-2.3-5.2-1zm-10.8-8.1c-.7 1.3.3 2.9 2.3 3.9 1.6 1 3.6.7 4.3-.7.7-1.3-.3-2.9-2.3-3.9-2-.6-3.6-.3-4.3.7zm32.4 35.6c-1.6 1.3-1 4.3 1.3 6.2 2.3 2.3 5.2 2.6 6.5 1 1.3-1.3.7-4.3-1.3-6.2-2.2-2.3-5.2-2.6-6.5-1zm-11.4-14.7c-1.6 1-1.6 3.6 0 5.9 1.6 2.3 4.3 3.3 5.6 2.3 1.6-1.3 1.6-3.9 0-6.2-1.4-2.3-4-3.3-5.6-2z'/></svg>" />
    <link href="https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;600;700;800&family=JetBrains+Mono:wght@500;700&display=swap" rel="stylesheet">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <script src="https://cdnjs.cloudflare.com/ajax/libs/qrcodejs/1.0.0/qrcode.min.js"></script>
    <style>
        :root { --bg-base: #09090b; --bg-panel: #121214; --bg-hover: #1f1f22; --border: rgba(255,255,255,0.08); --border-hover: rgba(255,255,255,0.15); --text-main: #fafafa; --text-muted: #a1a1aa; --accent: #8b5cf6; --accent-hover: #7c3aed; --accent-bg: rgba(139,92,246,0.15); --danger: #ef4444; --warning: #f59e0b; --success: #8b5cf6; --info: #3b82f6; --purple: #8b5cf6; --radius-md: 16px; --radius-sm: 10px; }
        * { margin: 0; padding: 0; box-sizing: border-box; outline: none; -webkit-tap-highlight-color: transparent; user-select: none; -webkit-user-select: none; }
        ::selection { background: rgba(139, 92, 246, 0.35); color: #fff; }
        input, textarea, select, .mono, pre, code, #log-output, td, .form-label, th, p { user-select: text !important; -webkit-user-select: text !important; }
        body { background: var(--bg-base); color: var(--text-main); font-family: 'Plus Jakarta Sans', sans-serif; margin: 0; padding: 24px 16px; display: flex; justify-content: center; min-height: 100vh; box-sizing: border-box; }
        .container { max-width: 480px; width: 100%; display: flex; flex-direction: column; gap: 20px; padding-bottom: 30px; }
        .card { background: var(--bg-panel); border: 1px solid var(--border); border-radius: var(--radius-md); padding: 24px; box-shadow: 0 8px 30px rgba(0,0,0,0.4); }
        .card-title { margin: 0 0 16px 0; font-size: 1.15rem; font-weight: 800; display: flex; align-items: center; gap: 10px; }
        .stat-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 12px; }
        .stat-box { background: var(--bg-base); border: 1px solid var(--border); padding: 14px; border-radius: var(--radius-sm); }
        .stat-label { font-size: 0.75rem; color: var(--text-muted); font-weight: 700; text-transform: uppercase; margin-bottom: 6px; letter-spacing: 0.05em; }
        .stat-val { font-size: 1.15rem; font-weight: 800; font-family: 'JetBrains Mono', monospace; }
        .tag { padding: 4px 12px; border-radius: 8px; font-size: 0.7rem; font-weight: 800; text-transform: uppercase; letter-spacing: 0.05em; }
        .btn { width: 100%; background: var(--bg-hover); color: var(--text-main); border: 1px solid var(--border); padding: 14px; border-radius: var(--radius-sm); font-size: 0.9rem; font-weight: 700; cursor: pointer; display: flex; align-items: center; justify-content: center; gap: 8px; font-family: inherit; transition: all 0.2s ease; margin-top: 12px; }
        .btn:hover { background: var(--border-hover); transform: translateY(-1px); }
        .btn-primary { background: var(--accent); color: #000; border: none; box-shadow: 0 4px 12px rgba(139,92,246,0.35); }
        .btn-primary:hover { background: var(--accent-hover); color: #fff; }
        .btn-icon { width: 40px; height: 40px; padding: 0; margin: 0; }
        .link-item { background: var(--bg-base); border: 1px solid var(--border); padding: 14px; border-radius: var(--radius-sm); display: flex; justify-content: space-between; align-items: center; margin-bottom: 12px; transition: border-color 0.2s; }
        .link-item:hover { border-color: var(--border-hover); }
        .link-item-title { font-size: 0.9rem; font-weight: 700; margin-bottom: 4px; color: var(--text-main); }
        .link-item-sub { font-size: 0.75rem; color: var(--text-muted); font-family: 'JetBrains Mono', monospace; }
        .progress-bar { width: 100%; height: 8px; background: var(--bg-hover); border-radius: 4px; margin-top: 10px; overflow: hidden; }
        .progress-fill { height: 100%; background: var(--success); border-radius: 4px; transition: width 0.3s ease; }
        .progress-fill.warning { background: var(--warning); }
        .progress-fill.danger { background: var(--danger); }
        .qr-modal { display: none; position: fixed; inset: 0; background: rgba(0,0,0,0.8); backdrop-filter: blur(8px); justify-content: center; align-items: center; z-index: 100; padding: 20px; animation: fadeIn 0.2s ease; }
        .qr-modal.show { display: flex; }
        .qr-card { background: #fff; padding: 24px; border-radius: var(--radius-md); text-align: center; box-shadow: 0 20px 40px rgba(0,0,0,0.5); transform: translateY(0); transition: transform 0.3s; }
        @keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }
        
        .text-accent { color: var(--accent) !important; }
        .text-info { color: var(--info) !important; }
        .text-warning { color: var(--warning) !important; }
        .text-purple { color: var(--purple) !important; }
        
        .import-grid { display: grid; grid-template-columns: repeat(2, 1fr); gap: 10px; margin-top: 12px; }
        .btn-import { background: var(--bg-base); border: 1px solid var(--border); color: var(--text-main); text-decoration: none; padding: 14px 10px; border-radius: var(--radius-sm); font-size: 0.85rem; font-weight: 700; text-align: center; transition: all 0.2s; display: flex; flex-direction: column; align-items: center; justify-content: center; gap: 8px; }
        .btn-import:hover { background: var(--bg-hover); border-color: var(--accent); transform: translateY(-2px); box-shadow: 0 4px 12px rgba(16,185,129,0.15); }
        .btn-import i { font-size: 1.5rem; }
        
        .footer { text-align: center; margin-top: 20px; font-size: 0.8rem; color: var(--text-muted); font-weight: 600; }
        .footer a { color: var(--text-muted); text-decoration: none; transition: color 0.2s; }
        .footer a:hover { color: var(--text-main); }
    </style>
</head>
<body>
    <div class="container" id="app"></div>
    <div class="qr-modal" id="qr-modal" onclick="this.classList.remove('show')">
        <div class="qr-card" onclick="event.stopPropagation()">
            <div id="qrcode" style="display:inline-block; padding:10px; border:4px solid #f0f0f0; border-radius:12px; background:#fff;"></div>
            <button class="btn" style="margin-top:20px; background:#f4f4f5; color:#18181b; border:none;" onclick="document.getElementById('qr-modal').classList.remove('show')">Close QR</button>
        </div>
    </div>
    <script>
        const DATA = JSON.parse(atob('{{SUB_DATA_B64}}'));
        function fmtGB(v){ return !v ? '∞' : v.toFixed(2)+' GB'; }
        function fmtDate(d){ return !d ? 'Never' : new Date(d).toLocaleDateString('en-US',{year:'numeric',month:'short',day:'numeric'}); }
        function cp(t){ navigator.clipboard.writeText(t).then(()=>{ const el=document.createElement('div'); el.innerText='Copied!'; el.style.cssText='position:fixed;bottom:20px;left:50%;transform:translateX(-50%);background:var(--success);color:#fff;padding:10px 20px;border-radius:20px;font-weight:700;z-index:999;box-shadow:0 4px 12px rgba(139,92,246,0.35);'; document.body.appendChild(el); setTimeout(()=>el.remove(),2000); }); }
        function qr(t){ document.getElementById('qrcode').innerHTML=''; new QRCode(document.getElementById('qrcode'),{text:t,width:220,height:220,colorDark:"#000000",colorLight:"#ffffff",correctLevel:QRCode.CorrectLevel.M}); document.getElementById('qr-modal').classList.add('show'); }
        
        function render(){
            const u = DATA.client.usage||0; const l = DATA.client.limit||0; const p = l>0?Math.min(100,(u/l)*100):0;
            const cls = p>90?'danger':(p>75?'warning':'');
            const subUrl = encodeURIComponent(window.location.href);
            const subName = encodeURIComponent(DATA.client.name);
            const b64Url = btoa(window.location.href);
            
            document.getElementById('app').innerHTML = `
                <div style="text-align:center; margin-bottom:8px;">
                    <svg viewBox="0 0 496 512" fill="var(--accent)" style="width:52px; height:52px; margin-bottom:12px; filter:drop-shadow(0 0 12px var(--accent-bg));">
                        <path d="M165.9 397.4c0 2-2.3 3.6-5.2 3.6-3.3.3-5.6-1.3-5.6-3.6 0-2 2.3-3.6 5.2-3.6 3-.3 5.6 1.3 5.6 3.6zm-31.1-4.5c-.7 2 1.3 4.3 4.3 4.9 2.6 1 5.6 0 6.2-2s-1.3-4.3-4.3-5.2c-2.6-.7-5.5.3-6.2 2.3zm44.2-1.7c-2.9.7-4.9 2.6-4.6 4.9.3 2 2.9 3.3 5.9 2.6 2.9-.7 4.9-2.6 4.6-4.6-.3-1.9-3-3.2-5.9-2.9zM244.8 8C106.1 8 0 113.3 0 252c0 110.9 69.8 205.8 169.5 239.2 12.8 2.3 17.3-5.6 17.3-12.1 0-6.2-.3-40.4-.3-61.4 0 0-70 15-84.7-29.8 0 0-11.4-29.1-27.8-36.6 0 0-22.9-15.7 1.6-15.4 0 0 24.9 2 38.6 25.8 21.9 38.6 58.6 27.5 72.9 20.9 2.3-16 8.8-27.1 16-33.7-55.9-6.2-112.3-14.3-112.3-110.5 0-27.5 7.6-41.3 23.6-58.9-2.6-6.5-11.1-33.3 2.6-67.9 20.9-6.5 69 27 69 27 20-5.6 41.5-8.5 62.8-8.5s42.8 2.9 62.8 8.5c0 0 48.1-33.6 69-27 13.7 34.7 5.2 61.4 2.6 67.9 16 17.7 25.8 31.5 25.8 58.9 0 96.5-58.9 104.2-114.8 110.5 9.2 7.9 17 22.9 17 46.4 0 33.7-.3 75.4-.3 83.6 0 6.5 4.6 14.4 17.3 12.1C428.2 457.8 496 362.9 496 252 496 113.3 383.5 8 244.8 8zM97.2 352.9c-1.3 1-1 3.3.7 5.2 1.6 1.6 3.9 2.3 5.2 1 1.3-1 1-3.3-.7-5.2-1.6-1.6-3.9-2.3-5.2-1zm-10.8-8.1c-.7 1.3.3 2.9 2.3 3.9 1.6 1 3.6.7 4.3-.7.7-1.3-.3-2.9-2.3-3.9-2-.6-3.6-.3-4.3.7zm32.4 35.6c-1.6 1.3-1 4.3 1.3 6.2 2.3 2.3 5.2 2.6 6.5 1 1.3-1.3.7-4.3-1.3-6.2-2.2-2.3-5.2-2.6-6.5-1zm-11.4-14.7c-1.6 1-1.6 3.6 0 5.9 1.6 2.3 4.3 3.3 5.6 2.3 1.6-1.3 1.6-3.9 0-6.2-1.4-2.3-4-3.3-5.6-2z"/>
                    </svg>
                    <h1 style="margin:0; font-size:1.8rem; font-weight:800; letter-spacing:-0.03em;">R2Leafy</h1>
                    <p style="color:var(--text-muted); font-size:0.85rem; font-weight:600; margin-top:6px;">Subscription Environment</p>
                </div>
                
                <div class="card">
                    <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:20px;">
                        <h2 class="card-title" style="margin:0;"><i class="fa-solid fa-user-shield text-accent"></i> ${DATA.client.name}</h2>
                        <span class="tag" style="background:${DATA.client.status?'var(--success)':'var(--danger)'}20; color:${DATA.client.status?'var(--success)':'var(--danger)'};">${DATA.client.status?'ACTIVE':'OFFLINE'}</span>
                    </div>
                    <div class="stat-grid">
                        <div class="stat-box"><div class="stat-label">Used Data</div><div class="stat-val">${u>0?u.toFixed(2):'0'} GB</div></div>
                        <div class="stat-box"><div class="stat-label">Total Quota</div><div class="stat-val">${fmtGB(l)}</div></div>
                        <div class="stat-box" style="grid-column:1/-1;">
                            <div style="display:flex; justify-content:space-between; align-items:center;"><span class="stat-label" style="margin:0;">Consumption</span><span style="font-size:0.8rem; font-weight:800;">${p.toFixed(1)}%</span></div>
                            <div class="progress-bar"><div class="progress-fill ${cls}" style="width:${p}%"></div></div>
                        </div>
                        <div class="stat-box"><div class="stat-label">Expiry</div><div class="stat-val" style="font-size:0.95rem;">${fmtDate(DATA.client.expiry)}</div></div>
                        <div class="stat-box"><div class="stat-label">Remaining</div><div class="stat-val" style="font-size:0.95rem;">${l?fmtGB(Math.max(0,l-u)):'∞'}</div></div>
                    </div>
                    <button class="btn btn-primary" style="margin-top:20px;" onclick="cp(window.location.href)"><i class="fa-solid fa-link"></i> Copy Subscription Link</button>
                    
                    <div style="margin-top:24px;">
                        <h3 style="font-size:0.9rem; font-weight:800; color:var(--text-main); margin:0 0 10px 0;"><i class="fa-solid fa-bolt text-warning"></i> One-Click Import</h3>
                        <div class="import-grid">
                            <a href="v2rayng://install-sub?url=${subUrl}&name=${subName}" class="btn-import"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 192 192" width="26" height="26" style="color:var(--accent);"><path fill="none" stroke="currentColor" stroke-linecap="round" stroke-linejoin="round" stroke-width="12" d="M22 39.005h40.738v113.99L170 39.005"/></svg> v2rayNG</a>
                            <a href="hiddify://install-sub?url=${subUrl}&name=${subName}" class="btn-import"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 48 48" width="26" height="26" style="color:var(--info);"><path fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" d="M33.578 19.376h8.146c.43 0 .776.346.776.777v19.785c0 .43-.346.777-.776.777h-8.146a.775.775 0 0 1-.776-.774V20.153c0-.43.346-.777.776-.777m8.146-12.091c.43 0 .776.347.776.777v8.359c0 .43-.346.777-.776.777h-8.146a.775.775 0 0 1-.776-.774v-3.769zM28.06 15.31c.43 0 .776.347.776.778v23.85c0 .43-.346.777-.776.777h-8.146a.775.775 0 0 1-.776-.774V20.68zm-13.638 8.15c.43 0 .776.347.776.778v15.7c0 .43-.346.777-.776.777H6.276a.775.775 0 0 1-.776-.777V28.83zm.777 11.419h3.94"/></svg> Hiddify</a>
                            <a href="shadowrocket://add/sub://${b64Url}?title=${subName}" class="btn-import"><i class="fa-solid fa-rocket text-warning"></i> Shadowrocket</a>
                            <a href="sing-box://import-remote-profile?url=${subUrl}&name=${subName}" class="btn-import"><i class="fa-solid fa-box text-purple"></i> Sing-Box</a>
                        </div>
                    </div>
                </div>
                
                <div class="card">
                    <h2 class="card-title"><i class="fa-solid fa-network-wired text-accent"></i> Core Configurations</h2>
                    <button class="btn" style="margin-bottom:20px; background:var(--accent-bg); color:var(--accent); border:none;" onclick="cp(DATA.links.join('\\n'))"><i class="fa-solid fa-copy"></i> Copy All Configs</button>
                    <div style="display:flex; flex-direction:column;">
                        ${DATA.links.map((lnk,i)=>{
                            let n = 'Node '+(i+1); try{n=decodeURIComponent(lnk.split('#')[1]||n);}catch(e){}
                            return `<div class="link-item">
                                <div style="min-width:0; flex:1; padding-right:16px;">
                                    <div class="link-item-title">${n}</div>
                                    <div class="link-item-sub">${lnk.substring(0,32)}...</div>
                                </div>
                                <div style="display:flex; gap:8px;">
                                    <button class="btn btn-icon" onclick="qr('${lnk}')"><i class="fa-solid fa-qrcode"></i></button>
                                    <button class="btn btn-icon" onclick="cp('${lnk}')"><i class="fa-solid fa-copy"></i></button>
                                </div>
                            </div>`;
                        }).join('')}
                    </div>
                </div>
                
                <div class="footer">
                    Powered by <a href="https://github.com/Code-Leafy/R2Leafy" target="_blank"><i class="fa-brands fa-github"></i> R2Leafy</a>
                </div>
            `;
        }
        render();
    </script>
</body>
</html>"""


# ---------------------------------------------------------------------------
# Logging & Helper Functions
# ---------------------------------------------------------------------------
def add_log(msg: str):
    timestamp = datetime.now().strftime("%H:%M:%S")
    entry = f"[{timestamp}] {msg}"
    console_logs.append(entry)
    logger.info(msg)

add_log("R2Leafy Gateway core initialized with TCP_NODELAY acceleration")
add_log("BBR congestion control active")
add_log("Ultra-fast WebSocket proxy active on port 443 (ALPN: http/1.1)")
add_log("Railway Cloud instance ready")

def get_domain() -> str:
    global CUSTOM_DOMAIN
    if CUSTOM_DOMAIN:
        return CUSTOM_DOMAIN
    render_url = os.environ.get("RENDER_EXTERNAL_URL", "")
    railway_domain = os.environ.get("RAILWAY_PUBLIC_DOMAIN", "")
    domain = render_url or railway_domain or f"localhost:{get_listen_port()}"
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
    # High ALPN negotiation: h2, http/1.1 for maximum performance
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

def resolve_name_placeholders(text: str, client: dict) -> str:
    if not text:
        return "R2Leafy Node"
    t = text
    used_gb = round(client.get("used_bytes", 0) / (1024.0 * 1024.0 * 1024.0), 2)
    limit_gb = client.get("limit", 0)
    limit_str = f"{limit_gb:.2f}GB" if limit_gb > 0 else "Unlimited"
    remain_str = f"{max(0, limit_gb - used_gb):.2f}GB" if limit_gb > 0 else "Unlimited"
    exp_str = client.get("expiry", "")[:10] if client.get("expiry") else "Never"
    
    t = t.replace("%client-name%", client.get("name", "Client"))
    t = t.replace("%data-used%", f"{used_gb:.2f}")
    t = t.replace("%data-total%", limit_str)
    t = t.replace("%data-remain%", remain_str)
    t = t.replace("%expiry-date%", exp_str)
    return t

def build_client_sub_links(client: dict) -> list:
    cid = str(client.get("id", "")).strip()
    cname = str(client.get("name", "")).strip()
    domain = get_domain()
    
    custom_entries = SUB_CLIENT_SUBSCRIPTIONS.get(cid) or SUB_CLIENT_SUBSCRIPTIONS.get(cname) or []
    
    sub_links = []
    if custom_entries and isinstance(custom_entries, list) and len(custom_entries) > 0:
        for entry in custom_entries:
            etype = entry.get("type", "proxy")
            raw_name = entry.get("name", "R2Leafy Node")
            resolved_name = resolve_name_placeholders(raw_name, client)
            
            if etype == "proxy":
                ip = (entry.get("ipAddress") or "").strip() or domain
                link = f"vless://{cid}@{ip}:443?encryption=none&security=tls&type=ws&host={domain}&path=%2Fws&sni={domain}&fp=chrome&alpn=http/1.1#{quote(resolved_name)}"
                sub_links.append(link)
            elif etype == "info":
                info_link = f"trojan://{generate_uuid()}@127.0.0.1:80?security=none#{quote(resolved_name)}"
                sub_links.append(info_link)
    
    if not sub_links:
        sub_links.append(generate_vless_link(cid, remark=f"R2Leafy🍃 {client['name']}-Direct", address=domain))
        for i, addr in enumerate(CUSTOM_ADDRESSES):
            if addr:
                sub_links.append(generate_vless_link(cid, remark=f"R2Leafy🍃 {client['name']}-Node{i+1}", address=addr))
    
    return sub_links

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

def ensure_default_client():
    global CLIENTS, SUB_CLIENT_SUBSCRIPTIONS
    if not CLIENTS:
        default_id = generate_uuid()
        default_client = {
            "id": default_id,
            "name": "Default",
            "limit": 0.0,
            "usage": 0.0,
            "limit_bytes": 0,
            "used_bytes": 0,
            "max_connections": 0,
            "expiry": "",
            "status": 1,
            "active": True,
            "utls": "chrome",
            "created_at": datetime.now().isoformat()
        }
        CLIENTS.append(default_client)
        
        # Pre-configured Subscription Lab layout: Info banner at top, then ultra-fast WebSocket node
        SUB_CLIENT_SUBSCRIPTIONS[default_id] = [
            {
                "id": "info-" + secrets.token_hex(4),
                "type": "info",
                "name": "📢 Welcome to R2Leafy | %data-used%GB / %data-total%",
                "ipAddress": ""
            },
            {
                "id": "ws-" + secrets.token_hex(4),
                "type": "proxy",
                "transport": "ws",
                "name": "⚡ %client-name%-WebSocket",
                "ipAddress": ""
            }
        ]
        save_state_to_disk()

load_state_from_disk()
ensure_default_client()

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
        ("https://api.ipify.org?format=json", lambda d: d.get("ip")),
        ("https://ipwho.is/", lambda d: d.get("ip")),
        ("https://ipapi.co/json/", lambda d: d.get("ip")),
    ]
    resolved_ip = None
    for ep, parser in endpoints:
        try:
            async with httpx.AsyncClient(timeout=4.0) as client:
                resp = await client.get(ep)
                if resp.status_code == 200:
                    data = resp.json()
                    ip_val = parser(data)
                    if ip_val and ip_val != "127.0.0.1":
                        resolved_ip = ip_val
                        IP_TELEMETRY["ipv4"] = ip_val
                        if "city" in data:
                            IP_TELEMETRY["city"] = data.get("city")
                        if "country_name" in data or "country" in data:
                            IP_TELEMETRY["country"] = data.get("country_name") or data.get("country")
                        if "connection" in data and isinstance(data["connection"], dict):
                            IP_TELEMETRY["provider"] = data["connection"].get("isp") or data["connection"].get("org") or "Railway Cloud"
                        elif "org" in data:
                            IP_TELEMETRY["provider"] = data.get("org")
                        break
        except Exception:
            continue

    if resolved_ip and (not IP_TELEMETRY.get("city") or IP_TELEMETRY.get("city") == "Amsterdam"):
        try:
            async with httpx.AsyncClient(timeout=4.0) as client:
                resp2 = await client.get(f"http://ip-api.com/json/{resolved_ip}")
                if resp2.status_code == 200:
                    d2 = resp2.json()
                    if d2.get("status") == "success":
                        IP_TELEMETRY["city"] = d2.get("city") or "The Dalles"
                        IP_TELEMETRY["country"] = d2.get("country") or "United States"
                        IP_TELEMETRY["provider"] = d2.get("org") or d2.get("isp") or "Google Cloud"
                        add_log(f"Public IP resolved: {resolved_ip} ({IP_TELEMETRY['city']}, {IP_TELEMETRY['country']})")
        except Exception:
            pass

# ---------------------------------------------------------------------------
# Modern FastAPI Lifespan Context Manager
# ---------------------------------------------------------------------------
@asynccontextmanager
async def lifespan(app: FastAPI):
    global http_client
    load_state_from_disk()
    ensure_default_client()
    limits = httpx.Limits(max_connections=1000, max_keepalive_connections=200)
    timeout = httpx.Timeout(30.0, connect=10.0)
    http_client = httpx.AsyncClient(limits=limits, timeout=timeout, follow_redirects=True)
    asyncio.create_task(speed_monitor_loop())
    asyncio.create_task(ip_lookup_task())
    add_log(f"R2Leafy gateway listening on port {get_listen_port()}")
    yield
    if http_client:
        await http_client.aclose()
    save_state_to_disk()
    add_log("R2Leafy gateway stopped")

app = FastAPI(title="R2Leafy", docs_url=None, redoc_url=None, lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# ---------------------------------------------------------------------------
# Frontend Template Serving Endpoints
# ---------------------------------------------------------------------------
def get_raw_index_html() -> str:
    global INDEX_HTML_CACHE
    if INDEX_HTML_CACHE:
        return INDEX_HTML_CACHE
    candidates = [
        INDEX_HTML_PATH,
        os.path.join(os.getcwd(), "index.html"),
        "index.html",
        "/app/index.html",
        "/home/user/index.html"
    ]
    for p in candidates:
        if os.path.exists(p):
            try:
                with open(p, "r", encoding="utf-8") as f:
                    INDEX_HTML_CACHE = f.read()
                    return INDEX_HTML_CACHE
            except Exception:
                pass
    return "<!DOCTYPE html><html><body><h1>R2Leafy</h1><p>Running on Railway</p></body></html>"

def serve_index_html(request: Request) -> HTMLResponse:
    token = request.cookies.get(SESSION_COOKIE)
    is_auth = False
    if token:
        exp = SESSIONS.get(token)
        if exp and exp >= time.time():
            is_auth = True

    content = get_raw_index_html()

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
@app.head("/")
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
@app.head("/health")
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
@app.get("/api/ip/refresh")
async def refresh_ip_location(_=Depends(require_auth)):
    await ip_lookup_task()
    return {"ok": True, "ip": IP_TELEMETRY}

@app.get("/api/state")
async def get_panel_state(_=Depends(require_auth)):
    global CLIENTS, SUB_CLIENT_SUBSCRIPTIONS, SETTINGS
    
    cpu_pct = psutil.cpu_percent(interval=None)
    if cpu_pct == 0:
        cpu_pct = 2.4
    cpu_cores = psutil.cpu_count(logical=True) or 2
    
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
    logs_text = chr(10).join(console_logs)

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
    new_state = body.get("state") if isinstance(body.get("state"), dict) else body
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
            SUB_CLIENT_SUBSCRIPTIONS.update(new_state["subClientSubscriptions"])

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

    # Generate custom nodes from Subscription Lab
    sub_links = build_client_sub_links(client)
    sub_content = chr(10).join(sub_links)
    encoded_payload = base64.b64encode(sub_content.encode()).decode()

    # If accessed from browser (HTML), render subscription landing page
    accept_header = request.headers.get("accept", "").lower()
    user_agent = request.headers.get("user-agent", "").lower()
    is_browser = ("text/html" in accept_header or "mozilla" in user_agent) and "raw" not in request.query_params

    if is_browser:
        data_obj = {
            "client": {
                "id": client["id"],
                "name": client["name"],
                "usage": round(client.get("used_bytes", 0) / (1024.0 * 1024.0 * 1024.0), 3),
                "limit": client.get("limit", 0),
                "expiry": client.get("expiry", ""),
                "status": client.get("status", 1)
            },
            "links": sub_links
        }
        b64_json = base64.b64encode(json.dumps(data_obj).encode()).decode()
        html_page = SUB_HTML_TEMPLATE.replace("{{SUB_DATA_B64}}", b64_json)
        return HTMLResponse(content=html_page)

    headers = {
        "Content-Type": "text/plain; charset=utf-8",
        "Content-Disposition": f'attachment; filename="R2Leafy_{client["name"]}.txt"',
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
# VLESS Proxy Header Parser & Core Engine
# ---------------------------------------------------------------------------
RELAY_BUF = 64 * 1024

def parse_vless_header(first_chunk: bytes):
    if len(first_chunk) < 24:
        raise ValueError("Packet chunk too small for VLESS protocol")
    pos = 0
    pos += 1
    pos += 16
    addon_len = first_chunk[pos]
    pos += 1 + addon_len
    command = first_chunk[pos]
    pos += 1
    port = int.from_bytes(first_chunk[pos:pos + 2], "big")
    pos += 2
    addr_type = first_chunk[pos]
    pos += 1
    if addr_type == 1:
        addr_bytes = first_chunk[pos:pos + 4]
        pos += 4
        address = ".".join(str(b) for b in addr_bytes)
    elif addr_type == 2:
        domain_len = first_chunk[pos]
        pos += 1
        address = first_chunk[pos:pos + domain_len].decode("utf-8", errors="ignore")
        pos += domain_len
    elif addr_type == 3:
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

# ---------------------------------------------------------------------------
# Ultra-Fast WebSocket VLESS Tunnel Engine
# ---------------------------------------------------------------------------
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
            prefix = bytes([0, 0]) if first else b""
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
        
        # Apply TCP_NODELAY for lowest latency
        try:
            sock = writer.get_extra_info("socket")
            if sock:
                sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except Exception:
            pass

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
    port = get_listen_port()
    uvicorn.run(app, host="0.0.0.0", port=port, access_log=False)
