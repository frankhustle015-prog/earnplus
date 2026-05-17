#!/usr/bin/env python3
"""
EarnPlus Telegram Bot
--------------------
Full Telegram bot version of the EarnPlus platform.
Includes all features: manual/auto/wacash earning modes,
number management, leaderboard, referrals, withdrawals,
admin panel, and built‑in auto‑worker (Telethon) for auto mode.

Environment variables:
    TELEGRAM_BOT_TOKEN   - your bot token from BotFather
    WORKER_TG_SESSION    - Telethon session string (for auto mode)
    WORKER_API_ID        - API ID for Telethon
    WORKER_API_HASH      - API Hash for Telethon
    DB_FILE              - optional, path to database (default earnplus.db)
    PLATFORM_USER        - platform login username
    PLATFORM_PASS        - platform login password
    SHARED_SECRET        - internal secret (default Frankpat1@)
    BASE_URL             - platform API URL (default https://api.wsjobs-ng.com)

Admin Telegram ID is hardcoded: 7113000547
"""

import asyncio
import logging
import os
import sqlite3
import secrets
import hashlib
import threading
import random
import time
import re
import psycopg2
from psycopg2.extras import RealDictCursor
from contextlib import contextmanager
from datetime import datetime
from typing import Optional, Dict, Any, Tuple
import concurrent.futures

import requests
from requests.exceptions import Timeout, ConnectionError as ReqConnError

try:
    import bcrypt
    BCRYPT_AVAILABLE = True
except ImportError:
    BCRYPT_AVAILABLE = False
    logging.warning("bcrypt not installed — falling back to SHA-256")

# Telegram bot imports
from telegram import (
    Update, InlineKeyboardButton, InlineKeyboardMarkup,
    ReplyKeyboardMarkup, KeyboardButton, ReplyKeyboardRemove,
    InputFile
)
from telegram.ext import (
    Application, CommandHandler, CallbackQueryHandler,
    MessageHandler, filters, ConversationHandler, ContextTypes
)

# Global variables for bot
_application = None
_bot_loop = None  # ADD THIS LINE RIGHT HERE

# ----------------------------------------------------------------------
# Configuration
# ----------------------------------------------------------------------
BASE_URL = os.getenv("BASE_URL", "https://api.wsjobs-ng.com")
PLATFORM_USER = os.getenv("PLATFORM_USER", "Frankhustle")
PLATFORM_PASS = os.getenv("PLATFORM_PASS", "f11111")
DB_FILE = os.getenv("DB_FILE", "earnplus_telegram.db")
SECRET_KEY = os.getenv("SECRET_KEY", "earnplus_bot_secret")
TOKEN_EXPIRY_H = 72   # not used, kept for legacy
NGN_PER_POINT = 0.15  # only fallback, actual rates from settings
MAX_RETRIES = 6
POLL_INTERVAL = 3
UA = ("Mozilla/5.0 (Linux; Android 13; V2116 Build/TP1A.220624.014_NONFC) "
      "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/145.0.7632.120 Mobile Safari/537.36")
SHARED_SECRET = os.getenv("SHARED_SECRET", "Frankpat1@")

# PostgreSQL for Railway persistence
DATABASE_URL = os.getenv("DATABASE_URL")  # Railway auto-injects this

# ----------------------------------------------------------------------
# Task4U platform for hourly mode (separate from wsjob)
# ----------------------------------------------------------------------
TASK4U_BASE_URL = os.getenv("TASK4U_BASE_URL", "https://api.taskm4u.com")
TASK4U_USER = os.getenv("TASK4U_USER", "9167577481")
TASK4U_PASS_HASH = os.getenv("TASK4U_PASS_HASH", "ead68717fbb2411b902ed9ad8b2c0639")  # MD5 hash of actual password
task4u_session: dict = {}  # will store token, http session
task4u_lock = threading.Lock()

ADMIN_TELEGRAM_ID = 7113000547  # hardcoded admin

# For workgo1 (wacash mode)
WORKGO_BASE = "https://api.eiorjgoiej.com"
WORKGO_APP_TYPE = "2"
WORKGO_APP_VER = "1.0.15"
WORKGO_UA = ("Mozilla/5.0 (Linux; Android 13; V2116 Build/TP1A.220624.014_NONFC) "
             "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/147.0.7727.56 Mobile Safari/537.36")

# ----------------------------------------------------------------------
# Logging
# ----------------------------------------------------------------------
logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO
)
log = logging.getLogger("earnplus_bot")

# ----------------------------------------------------------------------
# Global variables for platform session and active pairs
# ----------------------------------------------------------------------
platform_session: dict = {}
platform_lock = threading.Lock()
active_pairs: dict = {}
pairs_lock = threading.Lock()

# Workgo1 session
_workgo_token = None
_workgo_lock = threading.Lock()
_wacash_pairs: dict = {}
_wacash_pairs_lock = threading.Lock()
_wacash_fire_lock = threading.Lock()

# ----------------------------------------------------------------------
# Database helpers (same as original)
# ----------------------------------------------------------------------
@contextmanager
def get_db():
    if DATABASE_URL:
        # PostgreSQL for Railway
        conn = psycopg2.connect(DATABASE_URL)
        try:
            yield conn
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()
    else:
        # SQLite for local testing
        conn = sqlite3.connect(DB_FILE, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        try:
            yield conn
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()

def _hash_pw(p):
    try:
        if BCRYPT_AVAILABLE:
            return bcrypt.hashpw(p.encode(), bcrypt.gensalt()).decode()
    except Exception as e:
        log.warning(f"bcrypt hash failed: {e}")
    return hashlib.sha256(p.encode()).hexdigest()

def _verify_pw(p, h):
    try:
        if BCRYPT_AVAILABLE and h and (h.startswith("$2b$") or h.startswith("$2a$")):
            return bcrypt.checkpw(p.encode(), h.encode())
    except Exception:
        pass
    return hashlib.sha256(p.encode()).hexdigest() == h

def get_setting(k, d=None):
    with get_db() as db:
        r = db.execute("SELECT value FROM settings WHERE key=?", (k,)).fetchone()
        return r["value"] if r else d

def set_setting(k, v):
    with get_db() as db:
        db.execute("INSERT OR REPLACE INTO settings VALUES(?,?)", (k, str(v)))

def get_earning_mode() -> str:
    return get_setting("earning_mode", "manual")

def _to_pts(ngn):
    """Convert naira amount to points using current rate."""
    npm = float(get_setting("naira_per_msg", "30"))
    ppm = int(get_setting("points_per_msg", "200"))
    return int(ngn / npm * ppm) if npm > 0 else 0

def _pts_per_msg():
    """Points earned per message."""
    return int(get_setting("points_per_msg", "200"))

def pts_to_ngn(points: int) -> float:
    """Convert points to NGN based on current rate"""
    npm = float(get_setting("naira_per_msg", "30"))
    ppm = int(get_setting("points_per_msg", "200"))
    return (points / ppm * npm) if ppm > 0 else 0

def _credit(db, uid, amt, desc, t="earn"):
    db.execute("UPDATE users SET balance=balance+? WHERE id=?", (amt, uid))
    db.execute("INSERT INTO transactions(user_id,type,amount,description) VALUES(?,?,?,?)",
               (uid, t, amt, desc))

def _debit(db, uid, amt, desc):
    db.execute("UPDATE users SET balance=balance-? WHERE id=?", (amt, uid))
    db.execute("INSERT INTO transactions(user_id,type,amount,description) VALUES(?,?,?,?)",
               (uid, "debit", amt, desc))

def _notify(db, user_id, title, body, ntype="info"):
    db.execute("INSERT INTO notifications(user_id,title,body,type) VALUES(?,?,?,?)",
               (user_id, title, body, ntype))
    # Send Telegram message if bot is available - need to get telegram_id from DB
    try:
        with get_db() as db2:
            row = db2.execute("SELECT telegram_id FROM users WHERE id=?", (user_id,)).fetchone()
            if row and row["telegram_id"]:
                asyncio.run_coroutine_threadsafe(
                    send_telegram(row["telegram_id"], f"*{title}*\n{body}", parse_mode="Markdown"),
                    _bot_loop
                )
    except Exception as e:
        log.error(f"_notify send failed: {e}")

def _admin_log(db, admin_id, action, target=None, detail=None):
    db.execute("INSERT INTO admin_logs(admin_id,action,target,detail) VALUES(?,?,?,?)",
               (admin_id, action, str(target) if target else None, detail))

def _increment_daily_msgs(db, user_id: int, count: int = 1):
    today = datetime.utcnow().strftime("%Y-%m-%d")
    db.execute(
        "INSERT INTO daily_msgs(user_id, date, msgs_count) VALUES(?,?,?) "
        "ON CONFLICT(user_id, date) DO UPDATE SET msgs_count=msgs_count+?",
        (user_id, today, count, count)
    )

def init_db():
    with get_db() as db:
        is_postgres = DATABASE_URL is not None
        
        if is_postgres:
            # PostgreSQL syntax
            db.execute("""
                CREATE TABLE IF NOT EXISTS users(
                    id SERIAL PRIMARY KEY,
                    telegram_id INTEGER UNIQUE,
                    username TEXT,
                    password TEXT,
                    is_admin INTEGER DEFAULT 0,
                    balance REAL DEFAULT 0,
                    referral_code TEXT UNIQUE,
                    referred_by INTEGER,
                    is_banned INTEGER DEFAULT 0,
                    created_at TIMESTAMP DEFAULT NOW(),
                    earning_mode TEXT DEFAULT 'manual'
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS auth_tokens(
                    token TEXT PRIMARY KEY,
                    user_id INTEGER NOT NULL,
                    expires_at TIMESTAMP NOT NULL
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS numbers(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER,
                    account TEXT NOT NULL,
                    wsid INTEGER,
                    status TEXT DEFAULT 'pairing',
                    pair_code TEXT,
                    msgs_sent INTEGER DEFAULT 0,
                    added_at TIMESTAMP DEFAULT NOW(),
                    hourly_status TEXT DEFAULT 'offline',
                    hourly_start_time TIMESTAMP,
                    last_hourly_payout_time TIMESTAMP,
                    platform_hours_at_start INTEGER DEFAULT 0,
                    total_hours_earned INTEGER DEFAULT 0,
                    UNIQUE(user_id, account)
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS auto_numbers(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER NOT NULL,
                    account TEXT NOT NULL,
                    acct_type TEXT DEFAULT 'personal',
                    send_limit TEXT DEFAULT 'nolimit',
                    status TEXT DEFAULT 'pending',
                    pair_code TEXT,
                    msgs_sent INTEGER DEFAULT 0,
                    added_at TIMESTAMP DEFAULT NOW(),
                    UNIQUE(user_id, account)
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS pending_tasks(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER NOT NULL,
                    account TEXT NOT NULL UNIQUE,
                    acct_type TEXT DEFAULT 'personal',
                    send_limit TEXT DEFAULT 'nolimit',
                    status TEXT DEFAULT 'pending',
                    created_at TIMESTAMP DEFAULT NOW()
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS bank_details(
                    user_id INTEGER PRIMARY KEY,
                    account_num TEXT,
                    account_name TEXT,
                    bank_name TEXT
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS trx_wallets(
                    user_id INTEGER PRIMARY KEY,
                    wallet_address TEXT
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS withdrawals(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER,
                    amount REAL,
                    method TEXT DEFAULT 'bank',
                    status TEXT DEFAULT 'pending',
                    reason TEXT,
                    bank_name TEXT,
                    account_num TEXT,
                    account_name TEXT,
                    wallet_addr TEXT,
                    trx_amount REAL,
                    tx_hash TEXT,
                    created_at TIMESTAMP DEFAULT NOW(),
                    updated_at TIMESTAMP,
                    pts_amount INTEGER DEFAULT 0
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS transactions(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER,
                    type TEXT,
                    amount REAL,
                    description TEXT,
                    created_at TIMESTAMP DEFAULT NOW()
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS settings(
                    key TEXT PRIMARY KEY,
                    value TEXT
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS wacash_numbers(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER NOT NULL,
                    account TEXT NOT NULL,
                    status TEXT DEFAULT 'pairing',
                    pair_code TEXT,
                    ws_id INTEGER,
                    wacash_token TEXT,
                    msgs_sent INTEGER DEFAULT 0,
                    added_at TIMESTAMP DEFAULT NOW(),
                    UNIQUE(user_id, account)
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS claim_codes(
                    id SERIAL PRIMARY KEY,
                    code TEXT UNIQUE NOT NULL,
                    points REAL NOT NULL,
                    note TEXT,
                    used_by INTEGER,
                    used_at TIMESTAMP,
                    created_at TIMESTAMP DEFAULT NOW()
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS notifications(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER,
                    title TEXT NOT NULL,
                    body TEXT NOT NULL,
                    type TEXT DEFAULT 'info',
                    is_read INTEGER DEFAULT 0,
                    created_at TIMESTAMP DEFAULT NOW()
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS admin_logs(
                    id SERIAL PRIMARY KEY,
                    admin_id INTEGER NOT NULL,
                    action TEXT NOT NULL,
                    target TEXT,
                    detail TEXT,
                    created_at TIMESTAMP DEFAULT NOW()
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS daily_msgs(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER NOT NULL,
                    date DATE NOT NULL,
                    msgs_count INTEGER DEFAULT 0,
                    UNIQUE(user_id, date)
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS check_ins(
                    id SERIAL PRIMARY KEY,
                    user_id INTEGER NOT NULL,
                    date DATE NOT NULL,
                    points_awarded INTEGER DEFAULT 50,
                    streak INTEGER DEFAULT 1,
                    UNIQUE(user_id, date)
                )
            """)
            
            db.execute("""
                CREATE TABLE IF NOT EXISTS login_attempts(
                    id SERIAL PRIMARY KEY,
                    username TEXT NOT NULL,
                    ip TEXT,
                    attempted_at TIMESTAMP DEFAULT NOW()
                )
            """)
            
            db.execute("CREATE INDEX IF NOT EXISTS idx_daily_msgs_date ON daily_msgs(date)")
            db.execute("CREATE INDEX IF NOT EXISTS idx_daily_msgs_uid ON daily_msgs(user_id)")
            
            # Insert settings (PostgreSQL syntax)
            settings_data = [
                ('naira_per_msg', '30.0'),
                ('points_per_msg', '200'),
                ('referral_pct', '5.0'),
                ('min_withdrawal', '15000'),
                ('max_withdrawal', '500000'),
                ('ngn_usd_rate', '1300.0'),
                ('trx_auto_payout', '1'),
                ('allow_registration', '1'),
                ('allow_withdrawals', '1'),
                ('platform_url', ''),
                ('trx_withdrawal_fee_usd', '0.20'),
                ('min_trx_withdrawal', '3.0'),
                ('earning_mode', 'manual'),
                ('wacash_account', ''),
                ('wacash_password', ''),
                ('wacash_fire_count', '100'),
                ('wacash_threads', '20'),
                ('hourly_rate_ngn', '5.0'),
                ('hourly_monitor_interval_seconds', '60'),
                ('hourly_payout_interval_minutes', '60'),
                ('hourly_enabled', '1')
            ]
            
            for key, value in settings_data:
                db.execute("INSERT INTO settings(key, value) VALUES(%s, %s) ON CONFLICT (key) DO NOTHING", (key, value))
            
            # Create default admin user
            admin = db.execute("SELECT id FROM users WHERE telegram_id = %s", (ADMIN_TELEGRAM_ID,)).fetchone()
            if not admin:
                ref = secrets.token_hex(4).upper()
                db.execute(
                    "INSERT INTO users(telegram_id, username, password, is_admin, referral_code) VALUES(%s, %s, %s, 1, %s)",
                    (ADMIN_TELEGRAM_ID, "admin", _hash_pw("admin123"), ref)
                )
                log.info("Admin user created (telegram_id=%s)", ADMIN_TELEGRAM_ID)
                
        else:
            # Original SQLite code (keep your existing SQLite creates)
            db.executescript("""
            CREATE TABLE IF NOT EXISTS users(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                telegram_id INTEGER UNIQUE,
                username TEXT,
                password TEXT,
                is_admin INTEGER DEFAULT 0,
                balance REAL DEFAULT 0,
                referral_code TEXT UNIQUE,
                referred_by INTEGER,
                is_banned INTEGER DEFAULT 0,
                created_at TEXT DEFAULT(datetime('now')));
            CREATE TABLE IF NOT EXISTS auth_tokens(
                token TEXT PRIMARY KEY, user_id INTEGER NOT NULL, expires_at TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS numbers(
                id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER,
                account TEXT NOT NULL, wsid INTEGER, status TEXT DEFAULT 'pairing',
                pair_code TEXT, msgs_sent INTEGER DEFAULT 0,
                added_at TEXT DEFAULT(datetime('now')), UNIQUE(user_id,account));
            CREATE TABLE IF NOT EXISTS auto_numbers(
                id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER NOT NULL,
                account TEXT NOT NULL, acct_type TEXT DEFAULT 'personal',
                send_limit TEXT DEFAULT 'nolimit', status TEXT DEFAULT 'pending',
                pair_code TEXT, msgs_sent INTEGER DEFAULT 0,
                added_at TEXT DEFAULT(datetime('now')), UNIQUE(user_id,account));
            CREATE TABLE IF NOT EXISTS pending_tasks(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                account TEXT NOT NULL UNIQUE,
                acct_type TEXT DEFAULT 'personal',
                send_limit TEXT DEFAULT 'nolimit',
                status TEXT DEFAULT 'pending',
                created_at TEXT DEFAULT(datetime('now')));
            CREATE TABLE IF NOT EXISTS bank_details(
                user_id INTEGER PRIMARY KEY, account_num TEXT, account_name TEXT, bank_name TEXT);
            CREATE TABLE IF NOT EXISTS trx_wallets(
                user_id INTEGER PRIMARY KEY, wallet_address TEXT);
            CREATE TABLE IF NOT EXISTS withdrawals(
                id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER,
                amount REAL, method TEXT DEFAULT 'bank', status TEXT DEFAULT 'pending',
                reason TEXT, bank_name TEXT, account_num TEXT, account_name TEXT,
                wallet_addr TEXT, trx_amount REAL, tx_hash TEXT,
                created_at TEXT DEFAULT(datetime('now')), updated_at TEXT, pts_amount INTEGER DEFAULT 0);
            CREATE TABLE IF NOT EXISTS transactions(
                id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER,
                type TEXT, amount REAL, description TEXT,
                created_at TEXT DEFAULT(datetime('now')));
            CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
            INSERT OR IGNORE INTO settings VALUES('naira_per_msg','30.0');
            INSERT OR IGNORE INTO settings VALUES('points_per_msg','200');
            INSERT OR IGNORE INTO settings VALUES('referral_pct','5.0');
            INSERT OR IGNORE INTO settings VALUES('min_withdrawal','15000');
            INSERT OR IGNORE INTO settings VALUES('max_withdrawal','500000');
            INSERT OR IGNORE INTO settings VALUES('ngn_usd_rate','1300.0');
            INSERT OR IGNORE INTO settings VALUES('trx_auto_payout','1');
            INSERT OR IGNORE INTO settings VALUES('allow_registration','1');
            INSERT OR IGNORE INTO settings VALUES('allow_withdrawals','1');
            INSERT OR IGNORE INTO settings VALUES('platform_url','');
            INSERT OR IGNORE INTO settings VALUES('trx_withdrawal_fee_usd','0.20');
            INSERT OR IGNORE INTO settings VALUES('min_trx_withdrawal','3.0');
            INSERT OR IGNORE INTO settings VALUES('earning_mode','manual');
            INSERT OR IGNORE INTO settings VALUES('wacash_account','');
            INSERT OR IGNORE INTO settings VALUES('wacash_password','');
            INSERT OR IGNORE INTO settings VALUES('wacash_fire_count','100');
            INSERT OR IGNORE INTO settings VALUES('wacash_threads','20');
            CREATE TABLE IF NOT EXISTS wacash_numbers(
                id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER NOT NULL,
                account TEXT NOT NULL, status TEXT DEFAULT 'pairing',
                pair_code TEXT, ws_id INTEGER, wacash_token TEXT,
                msgs_sent INTEGER DEFAULT 0,
                added_at TEXT DEFAULT(datetime('now')), UNIQUE(user_id,account));
            CREATE TABLE IF NOT EXISTS claim_codes(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                code TEXT UNIQUE NOT NULL, points REAL NOT NULL,
                note TEXT, used_by INTEGER, used_at TEXT,
                created_at TEXT DEFAULT(datetime('now')));
            CREATE TABLE IF NOT EXISTS notifications(
                id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER,
                title TEXT NOT NULL, body TEXT NOT NULL,
                type TEXT DEFAULT 'info', is_read INTEGER DEFAULT 0,
                created_at TEXT DEFAULT(datetime('now')));
            CREATE TABLE IF NOT EXISTS admin_logs(
                id INTEGER PRIMARY KEY AUTOINCREMENT, admin_id INTEGER NOT NULL,
                action TEXT NOT NULL, target TEXT, detail TEXT,
                created_at TEXT DEFAULT(datetime('now')));
            CREATE TABLE IF NOT EXISTS daily_msgs(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                date TEXT NOT NULL,
                msgs_count INTEGER DEFAULT 0,
                UNIQUE(user_id, date));
            CREATE TABLE IF NOT EXISTS check_ins(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                date TEXT NOT NULL,
                points_awarded INTEGER DEFAULT 50,
                streak INTEGER DEFAULT 1,
                UNIQUE(user_id, date));
            CREATE TABLE IF NOT EXISTS login_attempts(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT NOT NULL,
                ip TEXT,
                attempted_at TEXT DEFAULT(datetime('now')));
            CREATE INDEX IF NOT EXISTS idx_daily_msgs_date ON daily_msgs(date);
            CREATE INDEX IF NOT EXISTS idx_daily_msgs_uid ON daily_msgs(user_id);
            """)
            
            # SQLite hourly columns
            try:
                db.execute("ALTER TABLE numbers ADD COLUMN hourly_status TEXT DEFAULT 'offline'")
            except Exception: pass
            try:
                db.execute("ALTER TABLE numbers ADD COLUMN hourly_start_time TEXT")
            except Exception: pass
            try:
                db.execute("ALTER TABLE numbers ADD COLUMN last_hourly_payout_time TEXT")
            except Exception: pass
            try:
                db.execute("ALTER TABLE numbers ADD COLUMN platform_hours_at_start INTEGER DEFAULT 0")
            except Exception: pass
            try:
                db.execute("ALTER TABLE numbers ADD COLUMN total_hours_earned INTEGER DEFAULT 0")
            except Exception: pass
            
            try:
                db.execute("ALTER TABLE users ADD COLUMN earning_mode TEXT DEFAULT 'manual'")
            except Exception: pass
            
            db.execute("INSERT OR IGNORE INTO settings VALUES('hourly_rate_ngn', '5.0')")
            db.execute("INSERT OR IGNORE INTO settings VALUES('hourly_monitor_interval_seconds', '60')")
            db.execute("INSERT OR IGNORE INTO settings VALUES('hourly_payout_interval_minutes', '60')")
            db.execute("INSERT OR IGNORE INTO settings VALUES('hourly_enabled', '1')")
            
            try:
                db.execute("ALTER TABLE users ADD COLUMN telegram_id INTEGER UNIQUE")
            except Exception: pass
            try:
                db.execute("ALTER TABLE withdrawals ADD COLUMN pts_amount INTEGER DEFAULT 0")
            except Exception: pass
            
            # Create default admin user
            admin = db.execute("SELECT id FROM users WHERE telegram_id=?", (ADMIN_TELEGRAM_ID,)).fetchone()
            if not admin:
                ref = secrets.token_hex(4).upper()
                db.execute(
                    "INSERT INTO users(telegram_id,username,password,is_admin,referral_code) VALUES(?,?,?,1,?)",
                    (ADMIN_TELEGRAM_ID, "admin", _hash_pw("admin123"), ref)
                )
                log.info("Admin user created (telegram_id=%s)", ADMIN_TELEGRAM_ID)

# ----------------------------------------------------------------------
# Platform API functions (unchanged from original)
# ----------------------------------------------------------------------
def _md5(s): return hashlib.md5(s.encode()).hexdigest()
def _vhdrs():
    vt = str(int(time.time() * 1000))
    return {"verify-time": vt, "verify-encrypt": _md5("yh123456" + vt)}
def _hdrs(x=None):
    h = {"Content-Type": "application/json", "User-Agent": UA,
         "Referer": "https://www.wsjobs-ng.com/", "Origin": "https://www.wsjobs-ng.com",
         "accept": "application/json, text/plain, */*", "x-requested-with": "mark.via.gp"}
    h.update(_vhdrs())
    if x: h.update(x)
    return h
def _s0(p,u,n,tx=""): return _md5(_md5(p)+u+n+tx)
def _s1(p,u,n,tx=""): return _md5(_md5(p)+tx+u+n)
def _sa(p,u,n,a,t):   return _md5(_md5(p)+u+n+a+t)
def _retry(fn, label="API"):
    for i in range(1, MAX_RETRIES+1):
        try: return fn()
        except (Timeout, ReqConnError) as e:
            time.sleep(min(2**i, 20)); log.warning(f"[{label}] retry {i}: {e}")
        except Exception as e:
            time.sleep(min(2**i, 20)); log.warning(f"[{label}] error {i}: {e}")
    raise Exception(f"[{label}] Failed")

def platform_login():
    http = requests.Session()
    pm = _md5(_md5(PLATFORM_PASS))
    sign = _md5(_md5("/api/user/login") + PLATFORM_USER + pm)
    try:
        r = _retry(lambda: http.post(f"{BASE_URL}/api/user/login",
                   json={"username": PLATFORM_USER, "userpwd": pm, "sign": sign},
                   headers=_hdrs(), timeout=15), "login")
        d = r.json()
        if d.get("code") == 0:
            info = d["data"]["info"]
            with platform_lock:
                platform_session.update({"userid": info["id"], "username": PLATFORM_USER, "http": http})
            log.info(f"Platform login OK uid={info['id']}"); return True
        log.error(f"Login failed: {d.get('message')}"); return False
    except Exception as e:
        log.error(f"Login exception: {e}"); return False

def _ps():
    with platform_lock:
        s = dict(platform_session)
    if not s.get("http") or not s.get("userid"):
        log.warning("[platform] Session lost — re-logging in...")
        platform_login()
        with platform_lock:
            s = dict(platform_session)
    return s

def api_get_code(account):
    s = _ps(); uid, uname = str(s["userid"]), s["username"]
    sign = _s1("/api/user/get_code", uid, uname, tx=account)
    try:
        r = _retry(lambda: s["http"].get(f"{BASE_URL}/api/user/get_code",
                   params={"account": account, "signType": "1", "username": uname, "userid": uid, "sign": sign},
                   headers=_hdrs(), timeout=10), f"code:{account}")
        d = r.json()
        return (str(d["data"]), "ok") if d.get("code") == 0 and d.get("data") else (None, d.get("message", ""))
    except Exception: return None, 'Service unavailable'

def api_phonestatus(account):
    s = _ps(); uid, uname = str(s["userid"]), s["username"]
    sign = _s0("/api/user/get_phonestatus", uid, uname, tx=account)
    try:
        r = _retry(lambda: s["http"].get(f"{BASE_URL}/api/user/get_phonestatus",
                   params={"account": account, "signType": "0", "username": uname, "userid": uid, "sign": sign},
                   headers=_hdrs(), timeout=8), f"status:{account}")
        d = r.json()
        return int(d["data"]) if d.get("code") == 0 else None
    except: return None

def api_addwsnumber(account, types=1):
    s = _ps(); uid, uname = str(s["userid"]), s["username"]
    sign = _sa("/api/user/addwsnumber", uid, uname, account, str(types))
    try:
        r = _retry(lambda: s["http"].post(f"{BASE_URL}/api/user/addwsnumber",
                   json={"account": account, "types": types, "username": uname, "userid": int(uid), "sign": sign},
                   headers=_hdrs(), timeout=15), f"addws:{account}")
        d = r.json(); return d.get("code") == 0, d.get("message", "")
    except Exception: return False, 'Service unavailable'

def api_sendmsg(phone, wsid):
    s = _ps(); uid, uname = str(s["userid"]), s["username"]
    sign = _s0("/api/user/sendmsg", uid, uname, tx=str(wsid))
    try:
        r = _retry(lambda: s["http"].post(f"{BASE_URL}/api/user/sendmsg",
                   json={"phone": phone, "wsid": wsid, "username": uname, "userid": int(uid), "sign": sign},
                   headers=_hdrs(), timeout=15), f"send:{phone}")
        d = r.json()
        ok = d.get("code") == 0
        return ok, ("" if ok else "Send failed — please try again")
    except Exception: return False, "Network timeout — please try again"

def api_get_wsid(account):
    s = _ps(); uid, uname = str(s["userid"]), s["username"]
    page = 1
    while True:
        sign = _s0("/api/user/get_appinfo", uid, uname)
        try:
            r = _retry(lambda: s["http"].get(f"{BASE_URL}/api/user/get_appinfo",
                       params={"page": page, "pagesize": 50, "username": uname, "userid": uid, "sign": sign},
                       headers=_hdrs(), timeout=15), f"wsid:{account}")
            d = r.json()
            if d.get("code") != 0: break
            chunk, total = d["data"]["list"], d["data"]["count"]
            for item in chunk:
                if str(item.get("wsnumber", "")).strip() == account: return item["id"]
            if page * 50 >= total or not chunk: break
            page += 1
        except: break
    return None

def api_appinfo(page=1, pagesize=50):
    s = _ps(); uid, uname = str(s["userid"]), s["username"]
    sign = _s0("/api/user/get_appinfo", uid, uname)
    try:
        r = _retry(lambda: s["http"].get(f"{BASE_URL}/api/user/get_appinfo",
                   params={"page": page, "pagesize": pagesize, "username": uname, "userid": uid, "sign": sign},
                   headers=_hdrs(), timeout=15), "appinfo")
        d = r.json()
        return (d["data"]["list"], d["data"]["count"]) if d.get("code") == 0 else ([], 0)
    except: return [], 0
    
def api_get_online_numbers_from_platform():
    """Return a set of accounts that are currently online (status == 1)."""
    s = _ps()
    uid, uname = str(s["userid"]), s["username"]
    try:
        # Use POST to /taskhosting/page endpoint
        r = s["http"].post(f"{BASE_URL}/taskhosting/page",
                           json={"page": 1, "limit": 100},
                           headers=_hdrs(),
                           timeout=15)
        d = r.json()
        if d.get("code") == 0 and d.get("data", {}).get("data"):
            online = []
            for item in d["data"]["data"]:
                if item.get("status") == 1:   # 1 = online
                    online.append(item["ws_account"])
            return set(online)
    except Exception as e:
        log.error(f"api_get_online_numbers error: {e}")
    return set()

def api_get_hosting_time(account: str) -> int | None:
    """Return hosting_time (hours online) for a specific number, or None if not found."""
    s = _ps()
    uid, uname = str(s["userid"]), s["username"]
    try:
        r = s["http"].post(f"{BASE_URL}/taskhosting/page",
                           json={"page": 1, "limit": 100},
                           headers=_hdrs(),
                           timeout=15)
        d = r.json()
        if d.get("code") == 0 and d.get("data", {}).get("data"):
            for item in d["data"]["data"]:
                if item.get("ws_account") == account:
                    return item.get("hosting_time", 0)
    except Exception as e:
        log.error(f"api_get_hosting_time({account}) error: {e}")
    return None
    
def api_get_pairing_code(account: str) -> tuple[str | None, str | None]:
    """
    POST /task/getwswebcode
    Returns (code, error_message)
    """
    s = _ps()
    try:
        r = s["http"].post(
            f"{BASE_URL}/task/getwswebcode",
            json={"ws_account": account},
            headers=_hdrs(),
            timeout=15
        )
        d = r.json()
        if d.get("code") == 0 and d.get("data", {}).get("code"):
            return d["data"]["code"], None
        return None, d.get("message", "Unknown error")
    except Exception as e:
        return None, str(e)


def api_check_pairing_status(task_id: str) -> tuple[int | None, str | None]:
    """
    POST /task/getpadqrcoderesult
    Returns (status, error_message) where status: 0=pairing, 1=success
    """
    s = _ps()
    try:
        r = s["http"].post(
            f"{BASE_URL}/task/getpadqrcoderesult",
            json={"id": task_id},
            headers=_hdrs(),
            timeout=15
        )
        d = r.json()
        if d.get("code") == 0:
            return d["data"].get("status"), None
        return None, d.get("message", "Unknown error")
    except Exception as e:
        return None, str(e)
        
# ===================== TASK4U API FUNCTIONS (UPDATED) =====================

def task4u_login() -> bool:
    """Login to Task4U platform with Cloudflare bypass."""
    global task4u_session
    with task4u_lock:
        # Try cloudscraper first, fallback to requests
        try:
            import cloudscraper
            http = cloudscraper.create_scraper(
                browser={
                    'browser': 'chrome',
                    'platform': 'android',
                    'desktop': False,
                    'mobile': True
                },
                delay=15,
                interpreter='nodejs'  # Helps with Cloudflare
            )
            log.info("[Task4U] Using cloudscraper for Cloudflare bypass")
        except ImportError:
            log.warning("[Task4U] cloudscraper not installed, falling back to requests")
            http = requests.Session()
            # Add requests adapters for better connection handling
            adapter = requests.adapters.HTTPAdapter(pool_connections=10, pool_maxsize=10, max_retries=3)
            http.mount('http://', adapter)
            http.mount('https://', adapter)
        
        # Realistic mobile headers
        headers = {
            "Content-Type": "application/json",
            "User-Agent": "Mozilla/5.0 (Linux; Android 14; SM-S911B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36",
            "Accept": "application/json, text/plain, */*",
            "Accept-Language": "en-US,en;q=0.9",
            "Accept-Encoding": "gzip, deflate, br",
            "Origin": "https://taskm4u.com",
            "Referer": "https://taskm4u.com/",
            "Sec-Ch-Ua": '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"',
            "Sec-Ch-Ua-Mobile": "?1",
            "Sec-Ch-Ua-Platform": "Android",
            "Sec-Fetch-Dest": "empty",
            "Sec-Fetch-Mode": "cors",
            "Sec-Fetch-Site": "same-site",
            "Cache-Control": "no-cache",
            "Pragma": "no-cache"
        }
        
        payload = {
            "user_name": TASK4U_USER,
            "pwd": TASK4U_PASS_HASH,
            "autologin": True,
            "lang": "",
            "device": "android",
            "mac": "",
            "httpRequestIndex": 0,
            "httpRequestCount": 1,
            "version": "1.0.0",
            "platform": "android"
        }
        
        # Retry logic with backoff
        for attempt in range(1, 4):
            try:
                log.info(f"[Task4U] Login attempt {attempt}/3")
                
                # Add delay between attempts (except first)
                if attempt > 1:
                    delay = attempt * 3
                    log.info(f"[Task4U] Waiting {delay}s before retry...")
                    time.sleep(delay)
                
                # Execute request
                r = http.post(
                    f"{TASK4U_BASE_URL}/login/login",
                    json=payload,
                    headers=headers,
                    timeout=60,
                    verify=True
                )
                
                log.info(f"[Task4U] Response status: {r.status_code}")
                
                # Handle Cloudflare block
                if r.status_code == 403:
                    log.error(f"[Task4U] Cloudflare block detected (attempt {attempt}/3)")
                    
                    # Try to get the Cloudflare challenge page info
                    if 'cf-browser-verification' in r.text or 'cloudflare' in r.text.lower():
                        log.error("[Task4U] Cloudflare browser verification required")
                        
                        # If we have cloudscraper, it should handle this
                        if 'cloudscraper' in str(type(http)):
                            log.info("[Task4U] cloudscraper active, should bypass Cloudflare")
                        else:
                            log.error("[Task4U] Install cloudscraper: pip install cloudscraper")
                    
                    if attempt < 3:
                        continue
                    else:
                        # Disable hourly mode on final failure
                        log.error("[Task4U] All login attempts failed due to Cloudflare")
                        set_setting("hourly_enabled", "0")
                        return False
                
                if r.status_code != 200:
                    log.error(f"[Task4U] Unexpected status code: {r.status_code}")
                    continue
                
                # Parse JSON response
                try:
                    d = r.json()
                except Exception as json_err:
                    log.error(f"[Task4U] JSON decode error: {json_err}")
                    log.debug(f"[Task4U] Raw response: {r.text[:500]}")
                    continue
                
                # Check response
                if d.get("code") == 0 and d.get("data", {}).get("token"):
                    token = d["data"]["token"]
                    uid = d["data"]["uid"]
                    
                    task4u_session = {
                        "token": token,
                        "uid": uid,
                        "http": http,
                        "login_time": time.time()
                    }
                    log.info(f"[Task4U] ✅ Login successful! uid={uid}")
                    log.info(f"[Task4U] Token: {token[:20]}...")
                    
                    # Test the token with a simple API call
                    test_r = http.post(
                        f"{TASK4U_BASE_URL}/taskhosting/page?token={token}",
                        json={"page": 1, "limit": 1},
                        headers=_task4u_headers(),
                        timeout=30
                    )
                    if test_r.status_code == 200:
                        log.info("[Task4U] Token verified - API accessible")
                    else:
                        log.warning(f"[Task4U] Token test returned {test_r.status_code}")
                    
                    return True
                else:
                    error_msg = d.get('msg', d.get('message', 'Unknown error'))
                    log.error(f"[Task4U] Login API error: code={d.get('code')}, msg={error_msg}")
                    
                    # Special error handling
                    if d.get('code') == 30000:
                        log.error("[Task4U] Account may be locked or requires verification")
                    
            except requests.exceptions.Timeout:
                log.error(f"[Task4U] Request timeout (attempt {attempt}/3)")
                if attempt == 3:
                    log.error("[Task4U] All attempts timed out - network issue?")
                    return False
                    
            except requests.exceptions.ConnectionError as e:
                log.error(f"[Task4U] Connection error: {e}")
                if attempt == 3:
                    return False
                    
            except Exception as e:
                log.error(f"[Task4U] Unexpected error: {e}")
                import traceback
                log.debug(traceback.format_exc())
                if attempt == 3:
                    return False
        
        return False


def _task4u_headers() -> dict:
    """Get headers for Task4U API calls with token."""
    return {
        "Content-Type": "application/json",
        "User-Agent": "Mozilla/5.0 (Linux; Android 14; SM-S911B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en-US,en;q=0.9",
        "Accept-Encoding": "gzip, deflate, br",
        "Origin": "https://taskm4u.com",
        "Referer": "https://taskm4u.com/",
        "Sec-Ch-Ua": '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"',
        "Sec-Ch-Ua-Mobile": "?1",
        "Sec-Ch-Ua-Platform": "Android",
        "Sec-Fetch-Dest": "empty",
        "Sec-Fetch-Mode": "cors",
        "Sec-Fetch-Site": "same-site",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
        "x-requested-with": "mark.via.gp",
    }


def _task4u_ps():
    """Get Task4U session, login if needed."""
    global task4u_session
    with task4u_lock:
        # Check if session exists and token is not expired (assuming 24hr expiry)
        if not task4u_session.get("token") or not task4u_session.get("http"):
            log.warning("[Task4U] Session missing — re-logging in...")
            task4u_login()
        elif task4u_session.get("login_time", 0) < time.time() - 82800:  # 23 hours
            log.warning("[Task4U] Token may be expired — refreshing...")
            task4u_login()
        return dict(task4u_session)


def task4u_get_pairing_code(account: str) -> tuple[str | None, str | None]:
    """
    POST /task/getwswebcode with enhanced retry logic
    Returns (code, error_message)
    """
    s = _task4u_ps()
    token = s.get("token")
    if not token:
        return None, "Not logged in"
    
    # Try multiple attempts with increasing delays
    for attempt in range(1, 6):  # 5 attempts total
        try:
            log.info(f"[Task4U] Getting pairing code for {account} (attempt {attempt}/5)")
            
            # Add delay between attempts to avoid rate limiting
            if attempt > 1:
                delay = attempt * 2
                log.info(f"[Task4U] Waiting {delay}s before retry...")
                time.sleep(delay)
            
            # Make the API call
            r = s["http"].post(
                f"{TASK4U_BASE_URL}/task/getwswebcode",
                params={"token": token},
                json={"ws_account": account},
                headers=_task4u_headers(),
                timeout=45
            )
            
            log.info(f"[Task4U] getwswebcode response status: {r.status_code}")
            
            if r.status_code == 403:
                log.warning(f"[Task4U] Cloudflare block on attempt {attempt}")
                if attempt < 5:
                    continue
                return None, "Cloudflare is blocking the request"
            
            if r.status_code != 200:
                log.warning(f"[Task4U] HTTP {r.status_code} on attempt {attempt}")
                if attempt < 5:
                    continue
                return None, f"HTTP {r.status_code}"
            
            # Parse response
            try:
                d = r.json()
            except Exception as json_err:
                log.error(f"[Task4U] JSON parse error: {json_err}")
                if attempt < 5:
                    continue
                return None, "Invalid response from server"
            
            log.info(f"[Task4U] API response: code={d.get('code')}, msg={d.get('msg', '')}")
            
            # Success - got pairing code
            if d.get("code") == 0 and d.get("data", {}).get("code"):
                code = d["data"]["code"]
                log.info(f"[Task4U] ✅ Got pairing code for {account}: {code}")
                return code, None
            
            # Token expired - re-login and retry
            if d.get("code") in (401, 403) or "token" in str(d.get("msg", "")).lower():
                log.warning("[Task4U] Token expired or invalid, re-logging...")
                task4u_login()
                # Get fresh session and token
                s = _task4u_ps()
                token = s.get("token")
                if token:
                    continue
                return None, "Authentication failed"
            
            # Rate limited - wait longer
            if d.get("code") == 429 or "rate" in str(d.get("msg", "")).lower():
                log.warning(f"[Task4U] Rate limited on attempt {attempt}")
                time.sleep(attempt * 5)
                continue
            
            # QR code generation failed (Cloudflare specific)
            if d.get("code") == 30000:
                log.warning(f"[Task4U] QR code generation failed (Cloudflare)")
                if attempt == 5:
                    return None, "QR code generation blocked by Cloudflare"
                continue
            
            # Other API error
            if attempt == 5:
                return None, d.get("msg", f"Unknown error (code {d.get('code')})")
            
        except requests.exceptions.Timeout:
            log.warning(f"[Task4U] Timeout on attempt {attempt}/5")
            if attempt == 5:
                return None, "Connection timeout - please try again"
            continue
            
        except Exception as e:
            log.error(f"[Task4U] Unexpected error: {e}")
            if attempt == 5:
                return None, str(e)
            continue
    
    return None, "Max retries exceeded"


def task4u_get_online_numbers() -> set:
    """
    POST /taskhosting/page
    Returns set of accounts that are currently online (status == 1)
    """
    s = _task4u_ps()
    token = s.get("token")
    if not token:
        return set()
    
    try:
        r = s["http"].post(
            f"{TASK4U_BASE_URL}/taskhosting/page",
            params={"token": token},
            json={"page": 1, "limit": 100},
            headers=_task4u_headers(),
            timeout=15
        )
        
        if r.status_code != 200:
            log.warning(f"[Task4U] get_online_numbers HTTP {r.status_code}")
            return set()
        
        d = r.json()
        
        if d.get("code") == 0 and d.get("data", {}).get("data"):
            online = set()
            for item in d["data"]["data"]:
                if item.get("status") == 1:  # 1 = online
                    online.add(item.get("ws_account"))
            log.info(f"[Task4U] Found {len(online)} online numbers")
            return online
        
        return set()
        
    except Exception as e:
        log.error(f"[Task4U] get_online_numbers error: {e}")
        return set()


def task4u_get_hosting_time(account: str) -> int | None:
    """
    Return hosting_time (hours online) for a specific number
    """
    s = _task4u_ps()
    token = s.get("token")
    if not token:
        return None
    
    try:
        r = s["http"].post(
            f"{TASK4U_BASE_URL}/taskhosting/page",
            params={"token": token},
            json={"page": 1, "limit": 100},
            headers=_task4u_headers(),
            timeout=15
        )
        
        if r.status_code != 200:
            return None
        
        d = r.json()
        
        if d.get("code") == 0 and d.get("data", {}).get("data"):
            for item in d["data"]["data"]:
                if item.get("ws_account") == account:
                    hosting_time = item.get("hosting_time", 0)
                    log.debug(f"[Task4U] {account} hosting_time={hosting_time}")
                    return hosting_time
        
        return None
        
    except Exception as e:
        log.error(f"[Task4U] get_hosting_time({account}) error: {e}")
        return None


def task4u_check_health() -> bool:
    """Check if Task4U API is accessible"""
    try:
        r = requests.get(
            f"{TASK4U_BASE_URL}/health",
            timeout=10,
            headers={"User-Agent": "Mozilla/5.0"}
        )
        return r.status_code == 200
    except:
        return False

# ----------------------------------------------------------------------
# Workgo1 (wacash) API functions
# ----------------------------------------------------------------------
def _whdrs(include_token: bool = True) -> dict:
    h = {
        "app-type": WORKGO_APP_TYPE,
        "app-version": WORKGO_APP_VER,
        "accept": "application/json",
        "content-type": "application/json",
        "accept-language": "en_US",
        "origin": "https://www.taskgo8.com",
        "referer": "https://www.taskgo8.com/",
        "user-agent": WORKGO_UA,
        "x-requested-with": "mark.via.gp",
    }
    if include_token:
        with _workgo_lock:
            tok = _workgo_token or ""
        h["app-token"] = tok
    return h

def wacash_api_get(path: str, params: dict = None, retries: int = 4):
    global _workgo_token
    for attempt in range(retries):
        try:
            r = requests.get(f"{WORKGO_BASE}{path}", params=params,
                             headers=_whdrs(), timeout=10)
            data = r.json()
            if data and (data.get("code") in (401, 403) or
                         "过期" in str(data.get("msg", "")) or
                         "登录" in str(data.get("msg", ""))):
                log.info("[TaskGo] Token expired — re-logging in...")
                if wacash_login(): continue
                else: return data
            return data
        except Exception:
            time.sleep(2)
    return None

def wacash_login() -> bool:
    global _workgo_token
    acct = get_setting("wacash_account", "")
    pwd = get_setting("wacash_password", "")
    if not acct or not pwd:
        log.warning("[TaskGo] No account/password configured")
        return False
    try:
        r = requests.get(f"{WORKGO_BASE}/app/login",
                         params={"account": acct, "password": pwd},
                         headers=_whdrs(include_token=False),
                         timeout=15)
        d = r.json()
        if d and d.get("code") == 200:
            with _workgo_lock:
                _workgo_token = d["data"]
            log.info(f"[TaskGo] Logged in as {acct}")
            return True
        log.error(f"[TaskGo] Login failed: {d}")
        return False
    except Exception as e:
        log.error(f"[TaskGo] Login error: {e}")
        return False

def wacash_get_pair_code(phone: str):
    clean = re.sub(r"\D", "", phone)
    d = wacash_api_get("/app/wsNumber/getLoginCode", {"phone": clean})
    if not d or d.get("code") != 200:
        err = d.get("msg", "No response") if d else "No response"
        return None, err
    return d.get("data", ""), None

def wacash_get_online() -> list:
    d = wacash_api_get("/app/wsNumber/online")
    if d and d.get("code") == 200:
        return d.get("data", [])
    return []

def wacash_send_msg(ws_id: int):
    d = wacash_api_get("/app/wsNumber/sendMsg", {"id": ws_id}, retries=2)
    if d is None: return False, "no response"
    code = d.get("code")
    msg = d.get("msg", "")
    if code == 200: return True, "ok"
    if any(x in msg.lower() for x in ["logout", "logged out", "offline"]):
        return False, "offline"
    return False, msg
    
def wacash_get_task_info() -> dict:
    """Get today's accurate task stats from workgo1 API."""
    d = wacash_api_get("/app/wsNumber/getTaskInfo")
    if d and d.get("code") == 200:
        data = d.get("data", {})
        return {
            "todaySendNum":    data.get("todaySendNum", 0),
            "todayPoints":     data.get("todayPoints", 0),
            "yesterdayPoints": data.get("yesterdayPoints", 0),
        }
    return {"todaySendNum": 0, "todayPoints": 0, "yesterdayPoints": 0}

def _wacash_pair_bg(user_id: int, account: str):
    # Get actual Telegram ID from database
    with get_db() as db:
        user_row = db.execute("SELECT telegram_id FROM users WHERE id=?", (user_id,)).fetchone()
        if not user_row or not user_row["telegram_id"]:
            log.error(f"[TaskGo:Pair] No telegram_id found for user {user_id}")
            return
        telegram_id = user_row["telegram_id"]
    
    log.info(f"[TaskGo:Pair] Start {account} uid={user_id} telegram_id={telegram_id}")
    with _wacash_pairs_lock:
        _wacash_pairs[account] = {"user_id": user_id, "cancelled": False}
    if not _workgo_token:
        wacash_login()
    account_clean = account.replace("+", "").replace(" ", "").strip()
    online = wacash_get_online()
    existing_ws_id = None
    for n in online:
        online_phone = str(n.get("wsAppNo", "")).replace("+", "").replace(" ", "").strip()
        if online_phone == account_clean:
            existing_ws_id = n["id"]
            break
    if existing_ws_id:
        log.info(f"[TaskGo:Pair] {account} already online ws_id={existing_ws_id}")
        with get_db() as db:
            db.execute(
                "UPDATE wacash_numbers SET status='online',ws_id=?,pair_code=NULL WHERE user_id=? AND account=?",
                (existing_ws_id, user_id, account))
        with _wacash_pairs_lock:
            _wacash_pairs.pop(account, None)
        asyncio.run_coroutine_threadsafe(send_telegram(telegram_id, f"✅ Number {account} is already online and ready!", parse_mode="Markdown"), _bot_loop)
        return
    pair_code = None
    for i in range(MAX_RETRIES):
        code, err = wacash_get_pair_code(account_clean)
        if code:
            pair_code = code
            break
        log.warning(f"[TaskGo:Pair] attempt {i+1} failed: {err}")
        time.sleep(min(i+1,5))
    if not pair_code:
        log.warning(f"[TaskGo:Pair] Could not get code for {account}")
        with get_db() as db:
            db.execute("UPDATE wacash_numbers SET status='error' WHERE user_id=? AND account=?", (user_id, account))
        asyncio.run_coroutine_threadsafe(send_telegram(telegram_id, f"❌ Failed to get pairing code for {account}", parse_mode="Markdown"), _bot_loop)
        with _wacash_pairs_lock:
            _wacash_pairs.pop(account, None)
        return
    with get_db() as db:
        db.execute("UPDATE wacash_numbers SET pair_code=?,status='pairing' WHERE user_id=? AND account=?",
                   (pair_code, user_id, account))
    asyncio.run_coroutine_threadsafe(
            send_telegram(
                telegram_id,
                f"🔐 *Pairing Code Ready!*\n"
                f"━━━━━━━━━━━━━━━━━━━━\n"
                f"📱 Number: `{account}`\n"
                f"🔑 Code: `{pair_code}`\n"
                f"━━━━━━━━━━━━━━━━━━━━\n\n"
                f"*Steps to link:*\n"
                f"1️⃣ Open WhatsApp\n"
                f"2️⃣ Go to Settings → Linked Devices\n"
                f"3️⃣ Tap Link a Device\n"
                f"4️⃣ Select *Link with phone number*\n"
                f"5️⃣ Enter the code above\n\n"
                f"⏳ Code expires in ~2 minutes. Act fast!",
                parse_mode="Markdown"
            ),
            _bot_loop
        )
    
    deadline = time.time() + 300
    ws_id = None
    while time.time() < deadline:
        with _wacash_pairs_lock:
            if _wacash_pairs.get(account, {}).get("cancelled"):
                with get_db() as db:
                    db.execute("DELETE FROM wacash_numbers WHERE user_id=? AND account=?", (user_id, account))
                _wacash_pairs.pop(account, None)
                return
        time.sleep(4)
        online = wacash_get_online()
        for n in online:
            online_phone = str(n.get("wsAppNo", "")).replace("+", "").replace(" ", "").strip()
            if online_phone == account_clean:
                ws_id = n["id"]
                break
        if ws_id:
            break
    if not ws_id:
        log.info(f"[TaskGo:Pair] Timeout waiting for {account}")
        with get_db() as db:
            db.execute("UPDATE wacash_numbers SET status='timeout' WHERE user_id=? AND account=?", (user_id, account))
        asyncio.run_coroutine_threadsafe(send_telegram(telegram_id, f"⏰ Timeout: {account} did not come online within 5 minutes.", parse_mode="Markdown"), _bot_loop)
        with _wacash_pairs_lock:
            _wacash_pairs.pop(account, None)
        return
    with get_db() as db:
        db.execute("UPDATE wacash_numbers SET status='online',ws_id=?,pair_code=NULL WHERE user_id=? AND account=?",
                   (ws_id, user_id, account))
    with _wacash_pairs_lock:
        _wacash_pairs.pop(account, None)
    asyncio.run_coroutine_threadsafe(send_telegram(telegram_id, f"✅ Number {account} is now online and ready to earn!", parse_mode="Markdown"), _bot_loop)
    log.info(f"[TaskGo:Pair] {account} ready ws_id={ws_id}")

# ----------------------------------------------------------------------
# Manual pairing background (for manual mode)
# ----------------------------------------------------------------------
def _next_number_variant(original: str, current: str,
                         country_prefix: str = None,
                         local_part: str = None) -> str | None:
    """
    Generate the next number variant by inserting an extra 0 in front
    of the local number part.

    When country_prefix and local_part are supplied (from space-separated input):
      country=234, local=9157338416
      variant 1 → 234 09157338416  (0 prepended to local)
      variant 2 → 234 009157338416
      variant 3 → 234 0009157338416
      variant 4 → None (max 4)

    Without prefix info (legacy / non-space input):
      inserts 0 after position 2 of the current number.
    """
    orig_clean = original.lstrip("+")
    curr_clean = current.lstrip("+")
    extra = len(curr_clean) - len(orig_clean)
    if extra >= 4:
        return None

    if country_prefix and local_part:
        # Insert extra 0s in front of the local part
        zeros = "0" * (extra + 1)
        return country_prefix + zeros + local_part

    # Legacy: insert 0 after growing position in full number
    insert_pos = 2 + extra
    if insert_pos >= len(curr_clean):
        return None
    return curr_clean[:insert_pos] + "0" + curr_clean[insert_pos:]


def _pair_bg(user_id: int, account: str):
    # Get actual Telegram ID from database
    with get_db() as db:
        user_row = db.execute("SELECT telegram_id FROM users WHERE id=?", (user_id,)).fetchone()
        if not user_row or not user_row["telegram_id"]:
            log.error(f"[Pair] No telegram_id found for user {user_id}")
            return
        telegram_id = user_row["telegram_id"]
    
    log.info(f"[Pair] Start {account} uid={user_id} telegram_id={telegram_id}")
    # Determine original number (first time = account itself, retry = passed from callback)
    with pairs_lock:
        existing     = active_pairs.get(account, {})
        existing_orig = existing.get("original", account)
        c_prefix     = existing.get("country_prefix")
        l_part       = existing.get("local_part")
        active_pairs[account] = {
            "user_id": user_id, "pair_code": None,
            "status": "pairing", "wsid": None, "cancelled": False,
            "original": existing_orig,
            "country_prefix": c_prefix, "local_part": l_part,
        }
    pair_code = None
    for i in range(MAX_RETRIES):
        code, _ = api_get_code(account)
        if code: pair_code = code; break
        time.sleep(min(i+1,5))
    with pairs_lock:
        if account in active_pairs: active_pairs[account]["pair_code"] = pair_code
    with get_db() as db:
        db.execute("UPDATE numbers SET pair_code=? WHERE user_id=? AND account=?",
                   (pair_code, user_id, account))
    if pair_code:
        # original_account stored in active_pairs when pairing started
        with pairs_lock:
            _ap   = active_pairs.get(account, {})
            orig  = _ap.get("original", account)
            c_pfx = _ap.get("country_prefix")
            l_prt = _ap.get("local_part")
        next_variant = _next_number_variant(orig, account, c_pfx, l_prt)

        btn_row = []
        if next_variant:
            btn_row.append(InlineKeyboardButton(
                f"🔄 Link Next: {next_variant}",
                callback_data=f"linkagain_{orig}__{next_variant}"
            ))
        else:
            btn_row.append(InlineKeyboardButton(
                f"🔄 Link Again",
                callback_data=f"linkagain_{orig}__{account}"
            ))

        link_again_kb = InlineKeyboardMarkup([btn_row])
        asyncio.run_coroutine_threadsafe(
            send_telegram(
                telegram_id,
                f"🔐 *Pairing Code Ready!*\n"
                f"━━━━━━━━━━━━━━━━━━━━\n"
                f"📱 Number: `{account}`\n"
                f"🔑 Code: `{pair_code}`\n"
                f"━━━━━━━━━━━━━━━━━━━━\n\n"
                f"*Steps to link:*\n"
                f"1️⃣ Open WhatsApp\n"
                f"2️⃣ Go to Settings → Linked Devices\n"
                f"3️⃣ Tap Link a Device\n"
                f"4️⃣ Select *Link with phone number*\n"
                f"5️⃣ Enter the code above\n\n"
                f"⏳ Code expires in ~3 minutes.\n"
                f"{'Tap below to try the next number variant.' if next_variant else 'No more variants — tap to retry this number.'}",
                parse_mode="Markdown",
                reply_markup=link_again_kb
            ),
            _bot_loop
        )
    else:
        with pairs_lock:
            _ap2  = active_pairs.get(account, {})
            orig  = _ap2.get("original", account)
            c_pfx = _ap2.get("country_prefix")
            l_prt = _ap2.get("local_part")
        next_variant = _next_number_variant(orig, account, c_pfx, l_prt)

        btn_label = f"🔄 Try Next: {next_variant}" if next_variant else "🔄 Try Again"
        next_num   = next_variant if next_variant else account
        link_again_kb = InlineKeyboardMarkup([[
            InlineKeyboardButton(btn_label, callback_data=f"linkagain_{orig}__{next_num}")
        ]])
        asyncio.run_coroutine_threadsafe(
            send_telegram(
                telegram_id,
                f"❌ Could not retrieve pairing code for `{account}`.\n"
                f"{'Tap below to try the next number in the sequence.' if next_variant else 'Tap to retry with the same number.'}",
                parse_mode="Markdown",
                reply_markup=link_again_kb
            ),
            _bot_loop
        )
        with pairs_lock:
            active_pairs.pop(account, None)
        return
    elapsed = 0; came_online = False
    while elapsed < 7200:
        with pairs_lock:
            if active_pairs.get(account, {}).get("cancelled"):
                with get_db() as db:
                    db.execute("DELETE FROM numbers WHERE user_id=? AND account=?", (user_id, account))
                active_pairs.pop(account, None)
                return
        if api_phonestatus(account) == 1:
            came_online = True
            break
        time.sleep(POLL_INTERVAL)
        elapsed += POLL_INTERVAL
    if not came_online:
        with get_db() as db:
            db.execute("DELETE FROM numbers WHERE user_id=? AND account=?", (user_id, account))
        active_pairs.pop(account, None)
        asyncio.run_coroutine_threadsafe(
            send_telegram(telegram_id, f"⏰ *Connection Timed Out*\n\n`{account}` did not come online within the 2-hour window.\nPlease ensure the pairing code was entered correctly and try again.", parse_mode="Markdown"), 
            _bot_loop
        )
        return
    # Attempt to register on platform — may already be registered if number
    # connected previously. Either way, fetch the wsid.
    ok, reg_msg = api_addwsnumber(account)
    log.info(f"[Pair] addwsnumber {account}: ok={ok} msg={reg_msg}")

    # Always attempt to fetch wsid, even if addwsnumber returns ok=False
    # (number may already exist on the platform)
    wsid = None
    time.sleep(3)
    for attempt in range(6):
        wsid = api_get_wsid(account)
        if wsid:
            break
        log.info(f"[Pair] wsid attempt {attempt+1}/6 for {account} — waiting...")
        time.sleep(4)

    if wsid:
        today = datetime.utcnow().strftime("%Y-%m-%d")
        with get_db() as db:
            db.execute(
                "UPDATE numbers SET status='online',wsid=?,pair_code=NULL WHERE user_id=? AND account=?",
                (wsid, user_id, account)
            )
            db.execute("DELETE FROM daily_msgs WHERE user_id=? AND date=?", (user_id, today))
        with pairs_lock:
            if account in active_pairs:
                active_pairs[account].update({"status": "online", "wsid": wsid})
        asyncio.run_coroutine_threadsafe(
            send_telegram(
                telegram_id,
                f"🟢 *Number Connected Successfully!*\n\n"
                f"📱 `{account}` is now online and ready to earn.\n"
                f"You may now use *Send All* to begin sending messages.",
                parse_mode="Markdown"
            ),
            _bot_loop
        )
        log.info(f"[Pair] ✅ Online {account} wsid={wsid}")
    else:
        # wsid still not found — number may not have completed linking
        log.warning(f"[Pair] wsid not found after retries for {account}")
        with get_db() as db:
            db.execute(
                "UPDATE numbers SET status='error' WHERE user_id=? AND account=?",
                (user_id, account)
            )
        with pairs_lock:
            if account in active_pairs: active_pairs[account]["status"] = "error"
        asyncio.run_coroutine_threadsafe(
            send_telegram(
                telegram_id,
                f"⚠️ *Linking Incomplete*\n\n"
                f"📱 `{account}` connected to WhatsApp but could not be registered on the platform.\n\n"
                f"Please use *Reauthorize* from My Numbers to retry.",
                parse_mode="Markdown"
            ),
            _bot_loop
        )
        
def _pair_hourly_bg(user_id: int, account: str):
    """
    Pair a number for hourly mode using Task4U API.
    """
    with get_db() as db:
        user_row = db.execute("SELECT telegram_id FROM users WHERE id=?", (user_id,)).fetchone()
        if not user_row or not user_row["telegram_id"]:
            log.error(f"[HourlyPair] No telegram_id for user {user_id}")
            return
        telegram_id = user_row["telegram_id"]

    log.info(f"[HourlyPair] Starting for {account} uid={user_id}")

    # Ensure Task4U is logged in
    with task4u_lock:
        if not task4u_session.get("token"):
            task4u_login()

    # Mark as pairing in DB
    with get_db() as db:
        db.execute(
            "UPDATE numbers SET status='pairing', hourly_status='pending' WHERE user_id=? AND account=?",
            (user_id, account)
        )

    # 1. Get pairing code using Task4U API
    code, err = task4u_get_pairing_code(account)
    if not code:
        asyncio.run_coroutine_threadsafe(
            send_telegram(telegram_id, f"❌ Failed to get pairing code for {account}: {err}"),
            _bot_loop
        )
        with get_db() as db:
            db.execute("UPDATE numbers SET status='error', hourly_status='offline' WHERE user_id=? AND account=?", (user_id, account))
        return

    # Store the code in DB (optional)
    with get_db() as db:
        db.execute("UPDATE numbers SET pair_code=? WHERE user_id=? AND account=?", (code, user_id, account))

    # Send code to user
    asyncio.run_coroutine_threadsafe(
        send_telegram(
            telegram_id,
            f"🔐 *Hourly Mode Pairing Code*\n\n"
            f"📱 Number: `{account}`\n"
            f"🔑 Code: `{code}`\n\n"
            f"1. Open WhatsApp → Settings → Linked Devices\n"
            f"2. Tap *Link a Device* → *Link with phone number*\n"
            f"3. Enter the code above\n\n"
            f"⏳ Code expires in ~2 minutes.\n\n"
            f"Once connected, you will automatically earn ₦{get_setting('hourly_rate_ngn','5')}/hour!",
            parse_mode="Markdown"
        ),
        _bot_loop
    )

    # 2. Poll for number to come online (max 5 minutes)
    deadline = time.time() + 300  # 5 minutes
    while time.time() < deadline:
        online_set = task4u_get_online_numbers()
        if account in online_set:
            # Success! Get hosting_time
            current_hours = task4u_get_hosting_time(account)
            with get_db() as db:
                db.execute("""
                    UPDATE numbers
                    SET status='online', hourly_status='online',
                        hourly_start_time = CURRENT_TIMESTAMP,
                        platform_hours_at_start = ?,
                        last_hourly_payout_time = CURRENT_TIMESTAMP,
                        pair_code = NULL
                    WHERE user_id=? AND account=?
                """, (current_hours or 0, user_id, account))
            asyncio.run_coroutine_threadsafe(
                send_telegram(
                    telegram_id,
                    f"✅ NUMBER ONLINE!\n\n"
                    f"📱 {account}\n"
                    f"💰 Mode: Hourly (₦{get_setting('hourly_rate_ngn','5')}/hour)\n"
                    f"🟢 Status: Online and earning\n\n"
                    f"You will earn ₦{get_setting('hourly_rate_ngn','5')} every hour automatically.",
                    parse_mode="Markdown"
                ),
                _bot_loop
            )
            return
        time.sleep(5)

    # Timeout
    with get_db() as db:
        db.execute("UPDATE numbers SET status='timeout', hourly_status='offline' WHERE user_id=? AND account=?", (user_id, account))
    asyncio.run_coroutine_threadsafe(
        send_telegram(telegram_id, f"⏰ Timeout: {account} did not come online within 5 minutes.\nPlease try again."),
        _bot_loop
    )

def _queue_task(user_id: int, account: str, acct_type: str, send_limit: str):
    """Insert a pending task into the queue for the Telethon worker to pick up."""
    with get_db() as db:
        db.execute(
            "INSERT OR REPLACE INTO pending_tasks(user_id,account,acct_type,send_limit,status,created_at) "
            "VALUES(?,?,?,?,'pending',datetime('now'))",
            (user_id, account, acct_type, send_limit)
        )
    log.info(f"[Queue] Task queued: {account} uid={user_id}")

def _cancel_queued_task(account: str):
    with get_db() as db:
        db.execute("DELETE FROM pending_tasks WHERE account=?", (account,))

# ----------------------------------------------------------------------
# Telegram bot helper to send messages asynchronously
# ----------------------------------------------------------------------
# Telegram bot helper to send messages asynchronously
_application = None  # will be set in main
_bot_loop = None  # ADD THIS LINE

async def send_telegram(telegram_id: int, text: str, reply_markup=None, parse_mode="HTML"):
    """Send a Telegram message to the given user ID."""
    global _application
    if _application is None:
        log.error("send_telegram called before application set")
        return
    try:
        # FIXED: use the parameter telegram_id, not undefined user_id
        await _application.bot.send_message(chat_id=telegram_id, text=text, reply_markup=reply_markup, parse_mode=parse_mode)
        log.info(f"✅ Message sent to {telegram_id}: {text[:50]}...")
    except Exception as e:
        log.error(f"Failed to send message to {telegram_id}: {e}")

# ----------------------------------------------------------------------
# Telethon worker for auto mode (copied from original, but modified to use send_telegram)
# ----------------------------------------------------------------------
_worker_client = None
_worker_bot_peer = None
_worker_bot_id = None
_worker_tasks: dict = {}
_worker_signals: dict = {}
_worker_refresh_loops: dict = {}
_worker_uid_cache: dict = {}
_worker_seen_ids: set = set()

# WORKER_SESSION: use env var, or fall back to hardcoded session string
# so auto mode works without needing to set WORKER_TG_SESSION separately
WORKER_SESSION  = os.environ.get("WORKER_TG_SESSION", "1BJWap1sBu1noXSVJvSrtb9GKsx-683FxlVg0jcBX_g8FC17hfMBA7IZbDOJ_GqSWvxopzrRO0WVuaPUMvop5DElVM3HjJqE-D5pd2pSJj6McJgH3luOb43VrFYRLyjaRMKAg4XuyvmmMfPMgf8Q1Fh-fveSqbQwOJc0ewAY-7dL_GZSPvOoqtaFMkcNoHLw_MelI363pyEZbWzimQXINYsEcIGJk9i9flHGzysukQbBijYOpYcC-xz5nYN-XCC3tFnHZUdDQpM1SBvDto0wZDa8MyLy2-E5rjVJgZRiuaPCxl72vQ8Brf66hihEmQqanpzV-px_8eCEaFoZ6Kh5HUi0Y6ZlEtaU=")
WORKER_API_ID   = int(os.environ.get("WORKER_API_ID",   "32641409"))
WORKER_API_HASH = os.environ.get("WORKER_API_HASH",     "38e7fff1f07ccd5c762af27d1d22b9c2")
WORKER_TARGET   = "@WStaskbot"

def _w_digits(n):
    return re.sub(r"\D", "", str(n))

def _w_find_cb(markup, cb_str):
    try:
        from telethon.tl.types import ReplyInlineMarkup, KeyboardButtonCallback
        if not markup or not isinstance(markup, ReplyInlineMarkup):
            return None
        target = cb_str.lower().strip()
        best = None
        for row in getattr(markup, "rows", []):
            for btn in getattr(row, "buttons", []):
                if not isinstance(btn, KeyboardButtonCallback):
                    continue
                cb = btn.data
                cb_s = cb.decode("utf-8", errors="replace") if isinstance(cb, bytes) else str(cb)
                cb_low = cb_s.lower().strip()
                if cb_low == target:
                    return cb_s
                if target in cb_low or cb_low in target:
                    best = cb_s
        return best
    except Exception:
        return None

def _w_extract_code(text):
    if not text:
        return None
    # Both letters and digits allowed, case‑insensitive
    m = re.search(r"([A-Z0-9]{4}[-][A-Z0-9]{4})", text, re.IGNORECASE)
    return m.group(1) if m else None

def _w_extract_number(text):
    if not text:
        return None
    m = re.search(r"(?:Number|Phone Number)[:\s]+(\+?[\d]{7,15})", text, re.IGNORECASE)
    if m:
        return m.group(1).strip()
    m = re.search(r"(?<!\d)(\d{10,15})(?!\d)", text)
    return m.group(1) if m else None

def _w_get_msg_text(m):
    return getattr(m, "raw_text", "") or getattr(m, "message", "") or ""

async def _w_click(msg_id, cb_str):
    from telethon.tl.functions.messages import GetBotCallbackAnswerRequest
    from telethon.errors import FloodWaitError
    for attempt in range(1, 4):
        try:
            await _worker_client(GetBotCallbackAnswerRequest(
                peer=_worker_bot_peer, msg_id=msg_id,
                data=cb_str.encode("utf-8"),
            ))
            return True
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 1)
        except Exception as e:
            log.error(f"[Worker:Click] {cb_str!r} attempt {attempt}: {e}")
            if attempt < 3:
                await asyncio.sleep(2)
    return False

async def _w_deliver_result(event, number, user_id, **kwargs):
    try:
        # Get the real Telegram ID from the database first
        with get_db() as db:
            user_row = db.execute("SELECT telegram_id FROM users WHERE id=?", (user_id,)).fetchone()
            if not user_row or not user_row["telegram_id"]:
                log.error(f"[Worker] No telegram_id found for user {user_id}")
                return
            telegram_id = user_row["telegram_id"]
        
        with get_db() as db:
            if event == "TASK_RESULT":
                code = kwargs.get("code", "")
                db.execute("UPDATE auto_numbers SET pair_code=? WHERE user_id=? AND account=?",
                           (code, user_id, number))
                await send_telegram(
                    telegram_id,
                    f"🔐 *Pairing Code Ready!*\n"
                    f"━━━━━━━━━━━━━━━━━━━━\n"
                    f"📱 Number: `{number}`\n"
                    f"🔑 Code: `{code}`\n"
                    f"━━━━━━━━━━━━━━━━━━━━\n\n"
                    f"*Steps to link:*\n"
                    f"1️⃣ Open WhatsApp\n"
                    f"2️⃣ Go to Settings → Linked Devices\n"
                    f"3️⃣ Tap Link a Device\n"
                    f"4️⃣ Select *Link with phone number*\n"
                    f"5️⃣ Enter the code above\n\n"
                    f"⏳ Code expires in ~2 minutes. Act fast!",
                    parse_mode="Markdown"
                )
            elif event == "PAIRED":
                db.execute("UPDATE auto_numbers SET status='online', pair_code=NULL WHERE user_id=? AND account=?",
                           (user_id, number))
                await send_telegram(
                    telegram_id,
                    f"✅ *Number Connected!*\n"
                    f"📱 `{number}` is now online and earning automatically.\n"
                    f"💡 You will be notified every time messages are sent and points are earned.\n"
                    f"📊 Check your dashboard to track earnings.",
                    parse_mode="Markdown"
                )
            elif event == "REWARD":
                # sent = new cumulative total; sent_delta = messages sent in this tick
                sent_delta = kwargs.get("sent_delta", 1)
                ppm = int(get_setting("points_per_msg", "200"))
                npm = float(get_setting("naira_per_msg", "30"))
                pts = ppm * sent_delta
                if pts > 0:
                    _credit(db, user_id, pts, f"Auto earn via {number} ({sent_delta} msg{'s' if sent_delta>1 else ''})")
                    _increment_daily_msgs(db, user_id, sent_delta)
                    db.execute(
                        "UPDATE auto_numbers SET msgs_sent=msgs_sent+? WHERE user_id=? AND account=?",
                        (sent_delta, user_id, number)
                    )
                    # Referral bonus
                    u_ref = db.execute("SELECT referred_by FROM users WHERE id=?", (user_id,)).fetchone()
                    if u_ref and u_ref["referred_by"]:
                        ref_bonus = max(1, int(pts * float(get_setting("referral_pct", "5")) / 100))
                        _credit(db, u_ref["referred_by"], ref_bonus,
                                f"Ref bonus from uid={user_id} auto", "referral")
                    bal = db.execute("SELECT balance FROM users WHERE id=?", (user_id,)).fetchone()
                    bal_pts = int(bal["balance"]) if bal else 0
                    ngn = pts_to_ngn(pts)
                    await send_telegram(
                        telegram_id,
                        f"💰 *+{pts:,} pts earned!*\n"
                        f"📱 Number: `{number}`\n"
                        f"✉️ Messages sent: `{sent_delta}`\n"
                        f"₦ Value: `₦{ngn:.2f}`\n"
                        f"💼 New balance: `{bal_pts:,} pts`",
                        parse_mode="Markdown"
                    )
            elif event == "BATCH_EARN":
                # Called when a "Sending Task Completed" message is received
                sent_delta = kwargs.get("sent_delta", 1)
                ppm = int(get_setting("points_per_msg", "200"))
                npm = float(get_setting("naira_per_msg", "30"))
                pts = ppm * sent_delta
                if pts > 0:
                    _credit(db, user_id, pts, f"Auto batch earn via {number} ({sent_delta} msg{'s' if sent_delta>1 else ''})")
                    _increment_daily_msgs(db, user_id, sent_delta)
                    db.execute(
                        "UPDATE auto_numbers SET msgs_sent = msgs_sent + ? WHERE user_id=? AND account=?",
                        (sent_delta, user_id, number)
                    )
                    # Referral bonus
                    u_ref = db.execute("SELECT referred_by FROM users WHERE id=?", (user_id,)).fetchone()
                    if u_ref and u_ref["referred_by"]:
                        ref_bonus = max(1, int(pts * float(get_setting("referral_pct", "5")) / 100))
                        _credit(db, u_ref["referred_by"], ref_bonus,
                                f"Ref bonus from uid={user_id} auto batch", "referral")
                    bal = db.execute("SELECT balance FROM users WHERE id=?", (user_id,)).fetchone()
                    bal_pts = int(bal["balance"]) if bal else 0
                    ngn = pts_to_ngn(pts)
                    await send_telegram(
                        telegram_id,
                        f"💰 *+{pts:,} pts earned!*\n"
                        f"📱 Number: `{number}`\n"
                        f"✉️ Batch messages: `{sent_delta}`\n"
                        f"₦ Value: `₦{ngn:.2f}`\n"
                        f"💼 New balance: `{bal_pts:,} pts`",
                        parse_mode="Markdown"
                    )
            elif event == "DISCONNECTED":
                db.execute("UPDATE auto_numbers SET status='offline' WHERE user_id=? AND account=?",
                           (user_id, number))
                await send_telegram(telegram_id, f"⚠️ Number {number} disconnected. It has been marked offline.",
                                    parse_mode="Markdown")
            elif event == "TASK_FAILED":
                reason = kwargs.get("reason", "Unknown")
                db.execute("UPDATE auto_numbers SET status='error' WHERE user_id=? AND account=?",
                           (user_id, number))
                await send_telegram(telegram_id, f"❌ {number} failed: {reason}", parse_mode="Markdown")
            # TASK_COMPLETED is now removed – we use BATCH_EARN instead
            # If you still want to log it, keep a dummy block:
            elif event == "TASK_COMPLETED":
                # Do nothing – keep the number online
                log.info(f"[Worker] Task completed message received for {number}, but keeping number online.")
    except Exception as e:
        log.error(f"[Worker] Deliver error: {e}")

async def _w_refresh_loop(number, user_id, login_msg_id):
    num_d = _w_digits(number)
    refresh_cb = f"refresh_login_info:{num_d}"
    last_sent = -1
    log.info(f"[Worker:Refresh] ▶ {number}")
    while True:
        await asyncio.sleep(5)
        try:
            clicked = await _w_click(login_msg_id, refresh_cb)
            if not clicked:
                continue
            await asyncio.sleep(1.5)
            msgs = await _worker_client.get_messages(WORKER_TARGET, ids=login_msg_id)
            msg = msgs if not isinstance(msgs, list) else (msgs[0] if msgs else None)
            if not msg:
                continue
            text = _w_get_msg_text(msg)
            try:
                status = re.search(r"Status:\s*(\w+)", text).group(1).lower()
                sent = int(re.search(r"Sent:\s*(\d+)", text).group(1))
            except Exception:
                continue
            if last_sent >= 0 and sent > last_sent:
                sent_delta = sent - last_sent
                await _w_deliver_result("REWARD", number, user_id, sent_delta=sent_delta)
            last_sent = sent
            if status == "offline":
                await _w_deliver_result("DISCONNECTED", number, user_id)
                break
        except asyncio.CancelledError:
            break
        except Exception as e:
            log.error(f"[Worker:Refresh] {number}: {e}")
    _worker_refresh_loops.pop(num_d, None)

def _w_start_refresh(number, user_id, login_msg_id):
    num_d = _w_digits(number)
    _worker_uid_cache[num_d] = user_id
    existing = _worker_refresh_loops.get(num_d)
    if existing and not existing.done():
        existing.cancel()
    t = asyncio.create_task(_w_refresh_loop(number, user_id, login_msg_id))
    _worker_refresh_loops[num_d] = t

async def _w_process_message(msg):
    text = _w_get_msg_text(msg)
    tlow = text.lower()
    msg_id = msg.id
    markup = getattr(msg, "reply_markup", None)
    text_clean = text.replace("+", "").replace(" ", "").replace("-", "")

    for num_d, sig in list(_worker_signals.items()):
        # More flexible number matching
        num_match = (num_d in text_clean or
                     num_d[-6:] in text_clean or
                     num_d[-8:] in text_clean or
                     any(num_d[i:i+6] in text_clean for i in range(0, len(num_d)-5, 3)))
        if not num_match:
            continue

        if not sig["type_evt"].is_set():
            # Try finding type button (personal/business etc)
            matched = _w_find_cb(markup, sig["type_cb"])
            if not matched and markup:
                # Fallback: look for any type: button
                from telethon.tl.types import ReplyInlineMarkup, KeyboardButtonCallback
                if isinstance(markup, ReplyInlineMarkup):
                    for row in getattr(markup, "rows", []):
                        for btn in getattr(row, "buttons", []):
                            if isinstance(btn, KeyboardButtonCallback):
                                cb = btn.data.decode("utf-8", errors="replace") if isinstance(btn.data, bytes) else str(btn.data)
                                if cb.startswith("type:"):
                                    matched = cb
                                    break
                        if matched:
                            break
            if matched:
                sig["type_msg"] = msg_id
                sig["type_cb_raw"] = matched
                sig["type_evt"].set()
                log.info(f"[Worker] ✅ Type button found: {matched}")
                return

        elif not sig["limit_evt"].is_set():
            # Allow limit button from same OR any newer message
            matched = _w_find_cb(markup, sig["limit_cb"])
            if not matched and markup:
                # Fallback: look for any limit: button
                from telethon.tl.types import ReplyInlineMarkup, KeyboardButtonCallback
                if isinstance(markup, ReplyInlineMarkup):
                    for row in getattr(markup, "rows", []):
                        for btn in getattr(row, "buttons", []):
                            if isinstance(btn, KeyboardButtonCallback):
                                cb = btn.data.decode("utf-8", errors="replace") if isinstance(btn.data, bytes) else str(btn.data)
                                if "limit:" in cb or "nolimit" in cb:
                                    matched = cb
                                    break
                        if matched:
                            break
            if matched:
                sig["type_msg"] = msg_id  # update to current msg
                sig["limit_cb_raw"] = matched
                sig["limit_evt"].set()
                log.info(f"[Worker] ✅ Limit button found: {matched}")
                return

        elif not sig["code_evt"].is_set():
            # Code can appear in any message mentioning this number
            if "pairing code" in tlow or "pair" in tlow or "code" in tlow:
                code = _w_extract_code(text)
                if code:
                    sig["code_val"] = code
                    sig["code_evt"].set()
                    log.info(f"[Worker] ✅ Pairing code found: {code}")
                    return
                # Also check inline buttons for code
                if markup:
                    from telethon.tl.types import ReplyInlineMarkup, KeyboardButtonCallback
                    if isinstance(markup, ReplyInlineMarkup):
                        for row in getattr(markup, "rows", []):
                            for btn in getattr(row, "buttons", []):
                                label = getattr(btn, "text", "").strip()
                                code = _w_extract_code(label)
                                if code:
                                    sig["code_val"] = code
                                    sig["code_evt"].set()
                                    log.info(f"[Worker] ✅ Code from button: {code}")
                                    return

        elif not sig["login_evt"].is_set():
            login_keywords = ("logged in successfully", "waiting for task dispatch",
                              "account has logged in", "currently sending",
                              "login success", "successfully linked", "connected")
            if any(kw in tlow for kw in login_keywords):
                sig["login_msg_id"] = msg_id
                sig["login_ok"] = True
                sig["login_evt"].set()
                log.info(f"[Worker] ✅ Login confirmed for signal")
                return
            if "authorization failed" in tlow or "auth failed" in tlow:
                sig["login_ok"] = False
                sig["login_evt"].set()
                return
    if msg_id in _worker_seen_ids:
        return
    _worker_seen_ids.add(msg_id)
    
    # Handle "Sending Task Completed" message – award points and keep number online
    if "sending task completed" in tlow:
        try:
            # Extract phone number (supports optional '+')
            number_match = re.search(r"-{5,}\s*\n(\+?\d{7,15})\s*\n", text)
            if not number_match:
                number_match = re.search(r"(\+?\d{7,15})", text)
            number = number_match.group(1) if number_match else None

            # Extract total successfully sent
            total_match = re.search(r"Total successfully sent:\s*(\d+)", text)
            total_sent = int(total_match.group(1)) if total_match else 0

            if number and total_sent > 0:
                uid = _worker_uid_cache.get(_w_digits(number))
                if uid:
                    # Award points for this batch (keeps number online)
                    await _w_deliver_result("BATCH_EARN", number, uid, sent_delta=total_sent)
                    log.info(f"[Worker] Completed task for {number}: +{total_sent} messages credited")
        except Exception as e:
            log.error(f"[Worker] Error parsing completion: {e}")
    
    if "authorization failed" in tlow:
        number = _w_extract_number(text)
        if number:
            uid = _worker_uid_cache.get(_w_digits(number))
            if uid:
                await _w_deliver_result("DISCONNECTED", number, uid, reason="Authorization failed")

async def _w_run_task(number, user_id, acct_type, send_limit):
    num_d = _w_digits(number)
    type_cb = f"type:{acct_type}"
    limit_cb = f"limit:{acct_type}:{send_limit}"
    log.info(f"[Worker:Task] ▶ START {number} type={acct_type} limit={send_limit}")
    sig = {
        "type_evt": asyncio.Event(), "type_msg": None, "type_cb_raw": type_cb,
        "limit_evt": asyncio.Event(), "limit_cb_raw": limit_cb,
        "code_evt": asyncio.Event(), "code_val": None,
        "login_evt": asyncio.Event(), "login_msg_id": None, "login_ok": False,
        "type_cb": type_cb, "limit_cb": limit_cb,
    }
    _worker_signals[num_d] = sig
    try:
        from telethon.errors import FloodWaitError
        for attempt in range(1, 4):
            try:
                await _worker_client.send_message(WORKER_TARGET, number)
                break
            except FloodWaitError as e:
                await asyncio.sleep(e.seconds + 1)
            except Exception as e:
                if attempt == 3:
                    raise Exception(f"Send failed: {e}")
                await asyncio.sleep(2)
        log.info(f"[Worker:Task] Waiting for type button for {number}...")
        await asyncio.wait_for(sig["type_evt"].wait(), timeout=180)
        log.info(f"[Worker:Task] Clicking type: {sig['type_cb_raw']}")
        clicked = await _w_click(sig["type_msg"], sig["type_cb_raw"])
        if not clicked:
            log.warning(f"[Worker:Task] Type click failed, retrying...")
            await asyncio.sleep(2)
            clicked = await _w_click(sig["type_msg"], sig["type_cb_raw"])
            if not clicked:
                raise Exception("Type click failed after retry")
        log.info(f"[Worker:Task] Waiting for limit button for {number}...")
        await asyncio.wait_for(sig["limit_evt"].wait(), timeout=180)
        log.info(f"[Worker:Task] Clicking limit: {sig['limit_cb_raw']}")
        clicked = await _w_click(sig["type_msg"], sig["limit_cb_raw"])
        if not clicked:
            log.warning(f"[Worker:Task] Limit click failed, retrying...")
            await asyncio.sleep(2)
            clicked = await _w_click(sig["type_msg"], sig["limit_cb_raw"])
            if not clicked:
                raise Exception("Limit click failed after retry")
        await asyncio.wait_for(sig["code_evt"].wait(), timeout=500)
        code = sig["code_val"]
        if not code:
            raise Exception("No pairing code")
        await _w_deliver_result("TASK_RESULT", number, user_id, code=code)
        await asyncio.wait_for(sig["login_evt"].wait(), timeout=420)
        if not sig["login_ok"]:
            raise Exception("Authorization failed")
        login_msg_id = sig["login_msg_id"]
        await _w_deliver_result("PAIRED", number, user_id)
        _worker_uid_cache[num_d] = user_id
        if login_msg_id:
            _w_start_refresh(number, user_id, login_msg_id)
        with get_db() as db:
            db.execute("UPDATE pending_tasks SET status='processed' WHERE account=?", (number,))
    except asyncio.CancelledError:
        raise
    except Exception as e:
        log.error(f"[Worker:Task] ❌ FAILED {number}: {e}")
        await _w_deliver_result("TASK_FAILED", number, user_id, reason=str(e))
        with get_db() as db:
            db.execute("UPDATE pending_tasks SET status='failed' WHERE account=?", (number,))
    finally:
        _worker_signals.pop(num_d, None)
        _worker_tasks.pop(number, None)

async def _w_task_poller():
    log.info("[Worker:Poller] ✅ Started")
    while True:
        await asyncio.sleep(3)
        try:
            if get_earning_mode() != "auto":
                continue
            with get_db() as db:
                tasks = db.execute(
                    "SELECT user_id, account, acct_type, send_limit FROM pending_tasks WHERE status='pending' LIMIT 5"
                ).fetchall()
            for row in tasks:
                user_id, account, acct_type, send_limit = row
                if account in _worker_tasks and not _worker_tasks[account].done():
                    continue
                log.info(f"[Worker:Poller] 📨 New task: {account} user={user_id}")
                with get_db() as db:
                    db.execute("UPDATE pending_tasks SET status='processing' WHERE account=?", (account,))
                _worker_uid_cache[_w_digits(account)] = user_id
                _worker_tasks[account] = asyncio.create_task(
                    _w_run_task(account, user_id, acct_type or "personal", send_limit or "nolimit")
                )
        except Exception as e:
            log.error(f"[Worker:Poller] Error: {e}")

async def _start_task_worker():
    global _worker_client, _worker_bot_peer, _worker_bot_id
    if not WORKER_SESSION:
        log.warning("[Worker] WORKER_TG_SESSION not set — task worker disabled")
        return
    try:
        from telethon import TelegramClient, events
        from telethon.sessions import StringSession
        _worker_client = TelegramClient(
            StringSession(WORKER_SESSION), WORKER_API_ID, WORKER_API_HASH,
            device_model="Samsung Galaxy S24",
            system_version="Android 14",
            app_version="10.14.0",
        )
        await _worker_client.start()
        me = await _worker_client.get_me()
        log.info(f"[Worker] ✅ Connected as {me.first_name}")
        bot_entity = await _worker_client.get_entity(WORKER_TARGET)
        _worker_bot_id = bot_entity.id
        _worker_bot_peer = await _worker_client.get_input_entity(WORKER_TARGET)
        @_worker_client.on(events.NewMessage(from_users=_worker_bot_id))
        async def on_bot_new(event):
            log.info(f"[Worker] 📨 New msg from bot: {_w_get_msg_text(event.message)[:80]}")
            await _w_process_message(event.message)

        @_worker_client.on(events.MessageEdited(from_users=_worker_bot_id))
        async def on_bot_edit(event):
            log.info(f"[Worker] ✏️ Edited msg from bot: {_w_get_msg_text(event.message)[:80]}")
            await _w_process_message(event.message)
        asyncio.create_task(_w_task_poller())
        log.info("[Worker] ✅ Task worker running!")
    except Exception as e:
        log.error(f"[Worker] Failed to start: {e}")
        
# ===================== HOURLY EARNING BACKGROUND TASKS =====================

async def handle_number_came_online(row):
    """Update DB when a number comes online (using Task4U API), notify user."""
    user_id = row["user_id"]
    account = row["account"]
    telegram_id = row["telegram_id"]

    # Ensure Task4U is logged in
    with task4u_lock:
        if not task4u_session.get("token"):
            task4u_login()

    current_hours = task4u_get_hosting_time(account)
    if current_hours is None:
        current_hours = 0

    with get_db() as db:
        db.execute("""
            UPDATE numbers
            SET hourly_status = 'online',
                hourly_start_time = CURRENT_TIMESTAMP,
                platform_hours_at_start = ?,
                last_hourly_payout_time = CURRENT_TIMESTAMP
            WHERE id = ?
        """, (current_hours, row["id"]))

    rate = get_setting("hourly_rate_ngn", "5.0")
    await send_telegram(
        telegram_id,
        f"✅ NUMBER ONLINE!\n\n"
        f"📱 {account}\n"
        f"💰 Mode: Hourly (₦{rate}/hour)\n"
        f"🟢 Status: Online and earning\n\n"
        f"You will earn ₦{rate} every hour automatically."
    )


async def handle_number_went_offline(row):
    """Mark number offline (using Task4U API), notify user."""
    user_id = row["user_id"]
    account = row["account"]
    telegram_id = row["telegram_id"]

    with get_db() as db:
        db.execute("""
            UPDATE numbers
            SET hourly_status = 'offline',
                hourly_start_time = NULL,
                platform_hours_at_start = 0
            WHERE id = ?
        """, (row["id"],))

    await send_telegram(
        telegram_id,
        f"⚠️ NUMBER OFFLINE ⚠️\n\n"
        f"📱 {account}\n"
        f"⏱ Was online until now.\n\n"
        f"➡️ Click Reauthorize to reconnect and resume earning!"
    )

async def realtime_hourly_monitor():
    """Runs every hour_monitor_interval seconds. Detects online/offline changes using Task4U API."""
    while True:
        try:
            if get_setting("hourly_enabled", "1") != "1":
                await asyncio.sleep(10)
                continue

            # Ensure Task4U is logged in
            with task4u_lock:
                if not task4u_session.get("token"):
                    task4u_login()

            with get_db() as db:
                rows = db.execute("""
                    SELECT n.id, n.user_id, n.account, n.hourly_status,
                           u.earning_mode, u.telegram_id
                    FROM numbers n
                    JOIN users u ON n.user_id = u.id
                    WHERE u.earning_mode = 'hourly'
                """).fetchall()
            if not rows:
                await asyncio.sleep(60)
                continue

            online_set = task4u_get_online_numbers()

            for row in rows:
                is_online = row["account"] in online_set
                if is_online and row["hourly_status"] != "online":
                    await handle_number_came_online(row)
                elif not is_online and row["hourly_status"] == "online":
                    await handle_number_went_offline(row)

        except Exception as e:
            log.error(f"realtime_hourly_monitor error: {e}")

        interval = int(get_setting("hourly_monitor_interval_seconds", "60"))
        await asyncio.sleep(interval)

async def hourly_payout_monitor():
    """Runs every hourly_payout_interval minutes. Credits users for full hours using Task4U API."""
    while True:
        try:
            if get_setting("hourly_enabled", "1") != "1":
                await asyncio.sleep(60)
                continue

            # Ensure Task4U is logged in
            with task4u_lock:  # Correct
                if not task4u_session.get("token"):
                    task4u_login()

            with get_db() as db:
                rows = db.execute("""
                    SELECT n.id, n.user_id, n.account, n.platform_hours_at_start,
                           n.last_hourly_payout_time, u.telegram_id
                    FROM numbers n
                    JOIN users u ON n.user_id = u.id
                    WHERE n.hourly_status = 'online'
                      AND u.earning_mode = 'hourly'
                """).fetchall()

            for row in rows:
                current_hours = task4u_get_hosting_time(row["account"])
                if current_hours is None:
                    continue

                last_hours = row["platform_hours_at_start"]
                new_hours = current_hours - last_hours
                if new_hours <= 0:
                    continue

                rate_ngn = float(get_setting("hourly_rate_ngn", "5.0"))
                amount_ngn = new_hours * rate_ngn
                points = _to_pts(amount_ngn)

                with get_db() as db2:
                    _credit(db2, row["user_id"], points,
                            f"Hourly earning for {row['account']} – {new_hours} hour(s)")
                    db2.execute("""
                        UPDATE numbers
                        SET platform_hours_at_start = ?,
                            last_hourly_payout_time = CURRENT_TIMESTAMP,
                            total_hours_earned = total_hours_earned + ?
                        WHERE id = ?
                    """, (current_hours, new_hours, row["id"]))

                    new_bal = db2.execute("SELECT balance FROM users WHERE id=?", (row["user_id"],)).fetchone()["balance"]
                    new_bal_ngn = pts_to_ngn(int(new_bal))

                await send_telegram(
                    row["telegram_id"],
                    f"💰 HOURLY EARNING! 💰\n\n"
                    f"📱 Number: `{row['account']}`\n"
                    f"⏱ Hours online: +{new_hours}\n"
                    f"💵 Earned: ₦{amount_ngn:.2f}\n"
                    f"💰 New balance: ₦{new_bal_ngn:,.2f}\n\n"
                    f"Keep your number online to keep earning!"
                )

        except Exception as e:
            log.error(f"hourly_payout_monitor error: {e}")

        interval = int(get_setting("hourly_payout_interval_minutes", "60")) * 60
        await asyncio.sleep(interval)
        
async def force_hourly_payout():
    """Force an immediate hourly payout check (for admin use) using Task4U API."""
    try:
        # Ensure Task4U is logged in
        with task4u_lock:
            if not task4u_session.get("token"):
                task4u_login()

        with get_db() as db:
            rows = db.execute("""
                SELECT n.id, n.user_id, n.account, n.platform_hours_at_start,
                       n.last_hourly_payout_time, u.telegram_id
                FROM numbers n
                JOIN users u ON n.user_id = u.id
                WHERE n.hourly_status = 'online'
                  AND u.earning_mode = 'hourly'
            """).fetchall()

        paid_count = 0
        for row in rows:
            current_hours = task4u_get_hosting_time(row["account"])
            if current_hours is None:
                continue

            last_hours = row["platform_hours_at_start"]
            new_hours = current_hours - last_hours
            if new_hours <= 0:
                continue

            rate_ngn = float(get_setting("hourly_rate_ngn", "5.0"))
            amount_ngn = new_hours * rate_ngn
            points = _to_pts(amount_ngn)

            with get_db() as db2:
                _credit(db2, row["user_id"], points,
                        f"Hourly earning for {row['account']} – {new_hours} hour(s) (forced)")
                db2.execute("""
                    UPDATE numbers
                    SET platform_hours_at_start = ?,
                        last_hourly_payout_time = CURRENT_TIMESTAMP,
                        total_hours_earned = total_hours_earned + ?
                    WHERE id = ?
                """, (current_hours, new_hours, row["id"]))
            paid_count += 1

        log.info(f"Force hourly payout completed: {paid_count} numbers paid")
    except Exception as e:
        log.error(f"force_hourly_payout error: {e}")

# ----------------------------------------------------------------------
# Telegram Bot Handlers
# ----------------------------------------------------------------------
# Conversation states
SELECTING_ACTION, TYPING_NUMBER, TYPING_AMOUNT, TYPING_PASSWORD, SELECTING_WITHDRAW_METHOD, TYPING_REFERRAL = range(6)
ADMIN_CREDIT_USER, ADMIN_BAN_USER, ADMIN_BROADCAST, ADMIN_SETTING_KEY, ADMIN_SETTING_VALUE, ADMIN_GEN_CODE, ADMIN_WITHDRAW_ACTION = range(10, 17)

# Main reply keyboard (visible to normal users and admin when not in admin panel)
main_keyboard = ReplyKeyboardMarkup([
    ["💰 Dashboard", "➕ Add Number", "📞 My Numbers"],
    ["⚡ Hourly Status", "✉️ Send All", "🏆 Leaderboard"],
    ["💸 Withdraw", "🔗 Referral", "⚙️ Settings"],
], resize_keyboard=True)

admin_extra_keyboard = ReplyKeyboardMarkup([
    ["👑 Admin Panel"]
], resize_keyboard=True)

# Admin panel keyboard (inline)
# Admin panel keyboard (inline)
admin_panel_buttons = [
    [InlineKeyboardButton("📊 Stats", callback_data="admin_stats")],
    [InlineKeyboardButton("👥 Users List", callback_data="admin_users")],
    [InlineKeyboardButton("✅ Approve Withdrawals", callback_data="admin_withdrawals")],
    [InlineKeyboardButton("💰 Credit User", callback_data="admin_credit")],
    [InlineKeyboardButton("⛔ Ban/Unban User", callback_data="admin_ban")],
    [InlineKeyboardButton("🔄 Switch Earning Mode", callback_data="admin_mode")],
    [InlineKeyboardButton("💰 Set Points per Message", callback_data="admin_points_per_msg")],
    [InlineKeyboardButton("💵 Set Naira per Point", callback_data="admin_naira_per_msg")],
    [InlineKeyboardButton("🎫 Generate Claim Code", callback_data="admin_gen_code")],
    [InlineKeyboardButton("📢 Broadcast", callback_data="admin_broadcast")],
    [InlineKeyboardButton("🔑 Set Wacash Credentials", callback_data="admin_set_wacash")],
    [InlineKeyboardButton("⚙️ Set Wacash Threads", callback_data="admin_set_threads")],
    [InlineKeyboardButton("🔐 Set Manual Login Creds", callback_data="admin_set_manual_creds")],
    [InlineKeyboardButton("🧪 Test Manual Login", callback_data="admin_test_manual_login")],
    # ========== NEW HOURLY ADMIN BUTTONS ==========
    [InlineKeyboardButton("💰 Set Hourly Rate", callback_data="admin_hourly_rate")],
    [InlineKeyboardButton("⏱ Set Hourly Interval", callback_data="admin_hourly_interval")],
    [InlineKeyboardButton("📊 Hourly Stats", callback_data="admin_hourly_stats")],
    [InlineKeyboardButton("🔄 Force Hourly Check", callback_data="admin_force_hourly")],
    # =============================================
    [InlineKeyboardButton("💾 Export Data", callback_data="admin_export")],
    [InlineKeyboardButton("📥 Import Data", callback_data="admin_import")],
    [InlineKeyboardButton("📜 Admin Logs", callback_data="admin_logs")],
    [InlineKeyboardButton("🔙 Back to User Menu", callback_data="admin_back")]
]
admin_panel_markup = InlineKeyboardMarkup(admin_panel_buttons)

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    telegram_id = user.id
    
    with get_db() as db:
        db_user = db.execute("SELECT id, is_admin, earning_mode FROM users WHERE telegram_id=?", (telegram_id,)).fetchone()
        if not db_user:
            # Create new user
            username = user.username or f"user{telegram_id}"
            ref_code = secrets.token_hex(5).upper()
            is_admin = 1 if telegram_id == ADMIN_TELEGRAM_ID else 0
            # New users start with NO earning_mode set (NULL)
            db.execute(
                "INSERT INTO users(telegram_id, username, password, referral_code, is_admin, earning_mode) VALUES(?,?,?,?,?, NULL)",
                (telegram_id, username, _hash_pw("default"), ref_code, is_admin)
            )
            new_id = db.execute("SELECT last_insert_rowid()").fetchone()[0]
            await send_telegram(telegram_id, f"Welcome {username}! Your account has been created.\n"
                                             f"Referral code: `{ref_code}`\n"
                                             f"Share it to earn bonuses.", parse_mode="Markdown")
            db_user = {"id": new_id, "is_admin": is_admin, "earning_mode": None}
        else:
            # Ensure is_admin matches Telegram ID
            if telegram_id == ADMIN_TELEGRAM_ID and not db_user["is_admin"]:
                db.execute("UPDATE users SET is_admin=1 WHERE telegram_id=?", (telegram_id,))
                db_user = db.execute("SELECT id, is_admin, earning_mode FROM users WHERE telegram_id=?", (telegram_id,)).fetchone()

    context.user_data["user_id"] = db_user["id"]
    context.user_data["is_admin"] = db_user["is_admin"]

    # ALWAYS show mode selection if user hasn't chosen a personal earning mode yet
    if not db_user["earning_mode"] or db_user["earning_mode"] == "" or db_user["earning_mode"] is None:
        keyboard = InlineKeyboardMarkup([
            [InlineKeyboardButton("💰 Manual Mode (Press Send All)", callback_data="set_mode_manual")],
            [InlineKeyboardButton("⚡ Hourly Mode (Auto-earn ₦5/hour)", callback_data="set_mode_hourly")]
        ])
        await update.message.reply_text(
            "🌟 *Welcome to EarnPlus Bot!* 🌟\n\n"
            "Please choose your preferred **earning mode**:\n\n"
            "💰 *Manual Mode* – You press 'Send All' to earn points\n"
            "⚡ *Hourly Mode* – Earn ₦5 per hour automatically while your number stays online\n\n"
            "💡 *Tip:* You can change this later in Settings → Personal Mode\n"
            "⚙️ *Admin Note:* Platform mode (Manual/Auto/Wacash) is separate from your personal earning mode.",
            reply_markup=keyboard, 
            parse_mode="Markdown"
        )
        return
    
    # User already has a personal mode set - show appropriate menu
    user_mode = db_user["earning_mode"]
    
    if db_user["is_admin"]:
        # Admin keyboard with Admin Panel button
        admin_keyboard = ReplyKeyboardMarkup([
            ["💰 Dashboard", "➕ Add Number", "📞 My Numbers"],
            ["⚡ Hourly Status", "✉️ Send All", "🏆 Leaderboard"],
            ["💸 Withdraw", "🔗 Referral", "⚙️ Settings"],
            ["👑 Admin Panel"]
        ], resize_keyboard=True)
        await update.message.reply_text(
            f"👋 Welcome back, *{user.first_name}*!\n\n"
            f"📌 Your personal earning mode: *{user_mode.upper()}*\n"
            f"🔧 Platform mode: *{get_earning_mode().upper()}*\n\n"
            f"Use the buttons below to navigate.",
            reply_markup=admin_keyboard,
            parse_mode="Markdown"
        )
    else:
        # Normal user keyboard
        await update.message.reply_text(
            f"👋 Welcome back, *{user.first_name}*!\n\n"
            f"📌 Your earning mode: *{user_mode.upper()}*\n\n"
            f"Use the buttons below to navigate.",
            reply_markup=main_keyboard,
            parse_mode="Markdown"
        )

async def mode_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    choice = query.data
    if choice == "mode_user":
        await query.edit_message_text("Switched to **User Mode**. You can now use the main menu.",
                                       parse_mode="Markdown")
        await query.message.reply_text("Main menu:", reply_markup=main_keyboard)
    elif choice == "mode_admin":
        await query.edit_message_text("Admin Panel:\nSelect an action:",
                                       reply_markup=admin_panel_markup)

# Helper to get internal user_id from telegram_id
def get_internal_user_id(telegram_id):
    with get_db() as db:
        row = db.execute("SELECT id FROM users WHERE telegram_id=?", (telegram_id,)).fetchone()
        return row["id"] if row else None
        
async def set_mode_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle user's earning mode selection from /start or settings"""
    query = update.callback_query
    await query.answer()
    mode = query.data.split("_")[-1]   # "manual" or "hourly"
    telegram_id = update.effective_user.id
    
    with get_db() as db:
        db.execute("UPDATE users SET earning_mode = ? WHERE telegram_id = ?", (mode, telegram_id))
        # Also update the user's data in context
        user = db.execute("SELECT id, is_admin FROM users WHERE telegram_id=?", (telegram_id,)).fetchone()
        if user:
            context.user_data["user_id"] = user["id"]
            context.user_data["is_admin"] = user["is_admin"]
    
    # Show confirmation with appropriate keyboard
    if context.user_data.get("is_admin"):
        admin_keyboard = ReplyKeyboardMarkup([
            ["💰 Dashboard", "➕ Add Number", "📞 My Numbers"],
            ["⚡ Hourly Status", "✉️ Send All", "🏆 Leaderboard"],
            ["💸 Withdraw", "🔗 Referral", "⚙️ Settings"],
            ["👑 Admin Panel"]
        ], resize_keyboard=True)
        await query.edit_message_text(
            f"✅ Mode set to **{mode.upper()}**!\n\n"
            f"💡 You can now use the main menu.",
            parse_mode="Markdown"
        )
        await query.message.reply_text("Main menu:", reply_markup=admin_keyboard)
    else:
        await query.edit_message_text(
            f"✅ Mode set to **{mode.upper()}**!\n\n"
            f"💡 Use the buttons below to start earning.",
            parse_mode="Markdown"
        )
        await query.message.reply_text("Main menu:", reply_markup=main_keyboard)

# Dashboard
async def dashboard(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start first.")
        return
    
    # Show spinner
    loading = await show_spinner(update, context, "📊 Fetching dashboard data")
    
    mode = get_earning_mode()
    today = datetime.utcnow().strftime("%Y-%m-%d")
    with get_db() as db:
        u = db.execute("SELECT balance, referral_code FROM users WHERE id=?", (uid,)).fetchone()
        te = db.execute("SELECT COALESCE(SUM(amount),0) as s FROM transactions WHERE user_id=? AND type='earn' AND date(created_at)=date('now')", (uid,)).fetchone()["s"]
        tr = db.execute("SELECT COALESCE(SUM(amount),0) as s FROM transactions WHERE user_id=? AND type='referral' AND date(created_at)=date('now')", (uid,)).fetchone()["s"]
        ta = db.execute("SELECT COALESCE(SUM(amount),0) as s FROM transactions WHERE user_id=? AND type='earn'", (uid,)).fetchone()["s"]
        msgs_today = db.execute(
            "SELECT COUNT(*) as c FROM transactions WHERE user_id=? AND type='earn' AND date(created_at)=date('now')",
            (uid,)).fetchone()["c"]
        total_msgs = db.execute("SELECT COUNT(*) as c FROM transactions WHERE user_id=? AND type='earn'", (uid,)).fetchone()["c"]
        if mode == "auto":
            online = db.execute("SELECT COUNT(*) as c FROM auto_numbers WHERE user_id=? AND status='online'", (uid,)).fetchone()["c"]
        elif mode == "wacash":
            online = db.execute("SELECT COUNT(*) as c FROM wacash_numbers WHERE user_id=? AND status='online'", (uid,)).fetchone()["c"]
        else:
            online = db.execute("SELECT COUNT(*) as c FROM numbers WHERE user_id=? AND status='online'", (uid,)).fetchone()["c"]
        checkin = db.execute("SELECT streak FROM check_ins WHERE user_id=? ORDER BY id DESC LIMIT 1", (uid,)).fetchone()
        streak = checkin["streak"] if checkin else 0
    
    pts_bal = int(u["balance"] or 0)
    naira_bal = pts_to_ngn(pts_bal)
    naira_today = pts_to_ngn(int(te or 0))
    naira_total = pts_to_ngn(int(ta or 0))
    
    text = (
        f"📊 *DASHBOARD*\n\n"
        f"💰 Balance: `{pts_bal:,}` pts\n"
        f"   ≈ ₦{naira_bal:,.2f}\n\n"
        f"📈 Today's earnings: `{int(te or 0):,}` pts (≈ ₦{naira_today:,.2f})\n"
        f"👥 Today's referral: `{int(tr or 0):,}` pts\n"
        f"🏆 Total earned: `{int(ta or 0):,}` pts (≈ ₦{naira_total:,.2f})\n\n"
        f"📱 Online numbers: `{online}`\n"
        f"✉️ Messages today: `{msgs_today}`\n"
        f"📬 Total messages: `{total_msgs}`\n"
        f"🔥 Check-in streak: `{streak}` day(s)\n"
        f"🔄 Mode: `{mode}`\n\n"
        f"🔗 Referral code: `{u['referral_code']}`"
    )
    
    await stop_spinner(context, text, success=True)
# Add number conversation
async def add_number_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    # Get user's personal earning mode from database
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    
    with get_db() as db:
        user_row = db.execute("SELECT earning_mode FROM users WHERE id=?", (uid,)).fetchone()
        user_mode = user_row["earning_mode"] if user_row else "manual"
    
    if user_mode == "manual":
        await update.message.reply_text(
            "📱 *Add Number — Manual Mode*\n\n"
            "Enter your number with the *country code and local number separated by a single space:*\n\n"
            "`234 9157338416`\n"
            "`31 97010531379`\n\n"
            "The space is required — it tells the system where the local number begins, "
            "so alternate prefixes can be tried automatically if needed.\n\n"
            "_Send /cancel to abort._",
            parse_mode="Markdown"
        )
    elif user_mode == "hourly":
        await update.message.reply_text(
            "📱 *Add Number — Hourly Mode*\n\n"
            "Enter your phone number in **international format** (numbers only):\n\n"
            "`2349157338416`\n"
            "`3197010545202`\n\n"
            "⚠️ **Important:**\n"
            "• Keep WhatsApp open on the linked device\n"
            "• You earn ₦5 per hour while the number stays online\n"
            "• You'll be notified when the number goes online/offline\n\n"
            "_Send /cancel to abort._",
            parse_mode="Markdown"
        )
    else:
        # Auto or Wacash mode handling
        platform_mode = get_earning_mode()
        if platform_mode == "wacash":
            await update.message.reply_text(
                "📱 *Add Number — Wacash Mode*\n\n"
                "Enter the phone number in international format:\n\n"
                "`2348012345678`\n\n"
                "_Send /cancel to abort._",
                parse_mode="Markdown"
            )
        else:
            await update.message.reply_text(
                "📱 *Add Number — Auto Mode*\n\n"
                "Enter the phone number in international format:\n\n"
                "`2348012345678`\n\n"
                "_Send /cancel to abort._",
                parse_mode="Markdown"
            )
    return TYPING_NUMBER

async def add_number_receive(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return ConversationHandler.END
    
    raw = update.message.text.strip()
    
    # Get user's personal earning mode (hourly/manual) - NOT the platform mode
    with get_db() as db:
        user_row = db.execute("SELECT earning_mode FROM users WHERE id=?", (uid,)).fetchone()
        user_mode = user_row["earning_mode"] if user_row else "manual"
    
    # Get platform mode for wacash/auto handling
    platform_mode = get_earning_mode()
    
    # ========== HOURLY MODE HANDLING ==========
    if user_mode == "hourly":
        # Hourly mode - add number to numbers table for hourly earning
        account = re.sub(r"[^\d]", "", raw)
        
        if len(account) < 7 or len(account) > 20:
            await update.message.reply_text(
                "⚠️ Invalid number format.\n"
                "Please use international format: `2349157338416`",
                parse_mode="Markdown"
            )
            return TYPING_NUMBER
        
        # Show spinner
        spinner = await show_spinner(update, context, "🔍 Checking number status for Hourly Mode")
        
        with get_db() as db:
            ex = db.execute("SELECT status FROM numbers WHERE user_id=? AND account=?", (uid, account)).fetchone()
            if ex and ex["status"] == "online":
                await stop_spinner(context, "This number is already linked and active on your account.", success=False)
                return ConversationHandler.END
            if ex:
                db.execute("""
                    UPDATE numbers 
                    SET status='pairing', pair_code=NULL, wsid=NULL, hourly_status='pending'
                    WHERE user_id=? AND account=?
                """, (uid, account))
            else:
                db.execute("""
                    INSERT INTO numbers(user_id, account, status, hourly_status) 
                    VALUES(?,?, 'pairing', 'pending')
                """, (uid, account))
        
        # No need to store in active_pairs for hourly mode – the new _pair_hourly_bg handles it
        
        await stop_spinner(context,
            "🔄 **Hourly Mode Pairing Initiated**\n\n"
            "You will receive your WhatsApp linking code shortly.\n"
            "Once connected, the number will be monitored **hourly**.\n"
            f"📍 Number: `{account}`\n\n"
            "⚠️ Keep WhatsApp open on this device to keep earning!",
            success=True,
            parse_mode="Markdown"
        )
        # Use the new hourly pairing function
        threading.Thread(target=_pair_hourly_bg, args=(uid, account), daemon=True).start()
        return ConversationHandler.END
    
    # ========== MANUAL MODE HANDLING ==========
    # Manual mode accepts "country_code local_number" with a space
    # e.g. "234 9157338416" or "31 97010531379"
    country_prefix = None
    local_part = None
    
    if platform_mode == "manual" and " " in raw:
        parts = raw.strip().split(None, 1)
        if len(parts) == 2:
            country_prefix = re.sub(r"[^\d]", "", parts[0])
            local_part     = re.sub(r"[^\d]", "", parts[1])
            account        = country_prefix + local_part
        else:
            account = re.sub(r"[^\d]", "", raw)
    else:
        account = re.sub(r"[^\d]", "", raw)

    if len(account) < 7 or len(account) > 20:
        await update.message.reply_text(
            "⚠️ The number you entered appears to be invalid.\n"
            "Please use international format with a space: `234 9157338416`",
            parse_mode="Markdown"
        )
        return TYPING_NUMBER

    # Store prefix/local for variant generation
    context.user_data["number_country_prefix"] = country_prefix
    context.user_data["number_local_part"]     = local_part
    context.user_data["pending_number"]        = account
    
    # Show spinner based on platform mode
    if platform_mode == "wacash":
        # Show spinner for Wacash mode
        spinner = await show_spinner(update, context, "Establishing connection to WorkGo1")
        
        if not _workgo_token:
            await update_spinner(context, "Authenticating with WorkGo1")
            wacash_login()
        
        with get_db() as db:
            ex = db.execute("SELECT status FROM wacash_numbers WHERE user_id=? AND account=?", (uid, account)).fetchone()
            if ex and ex["status"] == "online":
                await stop_spinner(context, "This number is already linked and active on your account.", success=False)
                return ConversationHandler.END
            if ex:
                db.execute("UPDATE wacash_numbers SET status='pairing',pair_code=NULL,ws_id=NULL,added_at=datetime('now') WHERE user_id=? AND account=?", (uid, account))
            else:
                db.execute("INSERT INTO wacash_numbers(user_id,account,status) VALUES(?,?,'pairing')", (uid, account))
        
        await stop_spinner(context, "Pairing initiated. You will receive your WhatsApp linking code shortly.", success=True)
        threading.Thread(target=_wacash_pair_bg, args=(uid, account), daemon=True).start()
        
    elif platform_mode == "auto":
        # Show spinner for Auto mode
        spinner = await show_spinner(update, context, "📌 Queueing for auto-pairing")
        
        acct_type = "personal"
        send_limit = "nolimit"
        with get_db() as db:
            ex = db.execute("SELECT status FROM auto_numbers WHERE user_id=? AND account=?", (uid, account)).fetchone()
            if ex and ex["status"] == "online":
                await stop_spinner(context, "This number is already linked and active on your account.", success=False)
                return ConversationHandler.END
            if ex:
                db.execute("UPDATE auto_numbers SET status='pending',added_at=datetime('now') WHERE user_id=? AND account=?", (uid, account))
            else:
                db.execute("INSERT INTO auto_numbers(user_id,account,acct_type,send_limit,status) VALUES(?,?,?,?,'pending')", (uid, account, acct_type, send_limit))
        
        _queue_task(uid, account, acct_type, send_limit)
        await stop_spinner(context, "Your number has been queued for auto-pairing. You will be notified as soon as your linking code is ready.", success=True)
        
    else:  # manual mode
        # Show spinner for Manual mode
        spinner = await show_spinner(update, context, "🔍 Checking number status")
        
        with get_db() as db:
            ex = db.execute("SELECT status FROM numbers WHERE user_id=? AND account=?", (uid, account)).fetchone()
            if ex and ex["status"] == "online":
                await stop_spinner(context, "This number is already linked and active on your account.", success=False)
                return ConversationHandler.END
            if ex:
                db.execute("UPDATE numbers SET status='pairing',pair_code=NULL,wsid=NULL WHERE user_id=? AND account=?", (uid, account))
            else:
                db.execute("INSERT INTO numbers(user_id,account,status) VALUES(?,?,'pairing')", (uid, account))
        
        # Store country_prefix/local_part in active_pairs before launching thread
        with pairs_lock:
            active_pairs[account] = {
                "user_id": uid, "pair_code": None, "status": "pairing",
                "wsid": None, "cancelled": False, "original": account,
                "country_prefix": context.user_data.get("number_country_prefix"),
                "local_part":     context.user_data.get("number_local_part"),
            }
        await stop_spinner(context,
            "Pairing initiated. You will receive your WhatsApp linking code shortly.",
            success=True)
        threading.Thread(target=_pair_bg, args=(uid, account), daemon=True).start()
    
    return ConversationHandler.END

async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Operation cancelled. Returning to the main menu.", reply_markup=main_keyboard)
    return ConversationHandler.END

# My Numbers
async def my_numbers(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return
    mode = get_earning_mode()
    today = datetime.utcnow().strftime("%Y-%m-%d")
    if mode == "wacash":
        with get_db() as db:
            rows = db.execute("SELECT account, status, pair_code, msgs_sent, ws_id as wsid, added_at FROM wacash_numbers WHERE user_id=? ORDER BY added_at DESC", (uid,)).fetchall()
    elif mode == "auto":
        with get_db() as db:
            rows = db.execute("SELECT account, status, pair_code, msgs_sent, added_at FROM auto_numbers WHERE user_id=? ORDER BY added_at DESC", (uid,)).fetchall()
    else:
        with get_db() as db:
            rows = db.execute("SELECT account, status, pair_code, msgs_sent, wsid, added_at FROM numbers WHERE user_id=? ORDER BY added_at DESC", (uid,)).fetchall()
    if not rows:
        await update.message.reply_text("You have no numbers connected yet. Use *Add Number* to link your first number.")
        return
    text = "*Your Numbers*\n\n"
    for r in rows:
        status = r["status"]
        status_emoji = "🟢" if status == "online" else "🟡" if status == "pairing" else "🔴"
        text += f"{status_emoji} `{r['account']}`\n"
        text += f"   Status: {status}\n"
        # FIXED: use dictionary-style access, not .get()
        if r["pair_code"]:
            text += f"   Code: `{r['pair_code']}`\n"
        text += f"   Messages sent total: {r['msgs_sent']}\n\n"
    await update.message.reply_text(text, parse_mode="Markdown")
    # Inline buttons to delete or reauthorize
    for r in rows:
        keyboard = InlineKeyboardMarkup([
            [InlineKeyboardButton("❌ Delete", callback_data=f"delnum_{r['account']}"),
             InlineKeyboardButton("🔄 Reauthorize", callback_data=f"reauthnum_{r['account']}")]
        ])
        await update.message.reply_text(f"Actions for {r['account']}:", reply_markup=keyboard)

async def number_action_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data = query.data
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await query.edit_message_text("Please use /start to register before proceeding.")
        return
    if data.startswith("delnum_"):
        account = data[7:]
        mode = get_earning_mode()
        if mode == "wacash":
            with _wacash_pairs_lock:
                if account in _wacash_pairs: _wacash_pairs[account]["cancelled"] = True
            with get_db() as db:
                db.execute("DELETE FROM wacash_numbers WHERE user_id=? AND account=?", (uid, account))
        elif mode == "auto":
            with get_db() as db:
                db.execute("DELETE FROM auto_numbers WHERE user_id=? AND account=?", (uid, account))
            _cancel_queued_task(account)
        else:
            with pairs_lock:
                if account in active_pairs: active_pairs[account]["cancelled"] = True
            with get_db() as db:
                db.execute("DELETE FROM numbers WHERE user_id=? AND account=?", (uid, account))
        await query.edit_message_text(f"✅ `{account}` has been removed from your account.")
    elif data.startswith("reauthnum_"):
        account = data[10:]
        mode = get_earning_mode()
        if mode == "wacash":
            with _wacash_pairs_lock:
                if account in _wacash_pairs: _wacash_pairs[account]["cancelled"] = True
            with get_db() as db:
                db.execute("UPDATE wacash_numbers SET status='pairing',pair_code=NULL,ws_id=NULL WHERE user_id=? AND account=?", (uid, account))
            await query.edit_message_text(f"🔄 Re-initiating pairing for `{account}`... Your linking code will arrive shortly.")
            threading.Thread(target=_wacash_pair_bg, args=(uid, account), daemon=True).start()
        elif mode == "auto":
            with get_db() as db:
                row = db.execute("SELECT acct_type,send_limit FROM auto_numbers WHERE user_id=? AND account=?", (uid, account)).fetchone()
                if row:
                    acct_type, send_limit = row["acct_type"], row["send_limit"]
                    db.execute("UPDATE auto_numbers SET status='pending' WHERE user_id=? AND account=?", (uid, account))
                    _cancel_queued_task(account)
                    _queue_task(uid, account, acct_type, send_limit)
                    await query.edit_message_text(f"📌 `{account}` has been queued for re-authorization. You will be notified when ready.")
                else:
                    await query.edit_message_text(f"Number {account} not found.")
        else:
            # For manual or hourly mode numbers (numbers table)
            with get_db() as db:
                # Check if user is in hourly mode
                user = db.execute("SELECT earning_mode FROM users WHERE id=?", (uid,)).fetchone()
                user_mode = user["earning_mode"] if user else "manual"
            
            with pairs_lock:
                if account in active_pairs:
                    active_pairs[account]["cancelled"] = True
            
            with get_db() as db:
                if user_mode == "hourly":
                    # Reset hourly-specific fields as well
                    db.execute("""
                        UPDATE numbers 
                        SET status='pairing', 
                            pair_code=NULL, 
                            wsid=NULL,
                            hourly_status='pending',
                            hourly_start_time=NULL,
                            platform_hours_at_start=0,
                            last_hourly_payout_time=NULL
                        WHERE user_id=? AND account=?
                    """, (uid, account))
                else:
                    db.execute("UPDATE numbers SET status='pairing', pair_code=NULL, wsid=NULL WHERE user_id=? AND account=?", (uid, account))
            
            await query.edit_message_text(f"🔄 Re-initiating pairing for `{account}`... Your linking code will arrive shortly.")
            
            # Use the appropriate pairing function
            if user_mode == "hourly":
                threading.Thread(target=_pair_hourly_bg, args=(uid, account), daemon=True).start()
            else:
                threading.Thread(target=_pair_bg, args=(uid, account), daemon=True).start()

    elif data.startswith("linkagain_"):
        # Format: linkagain_{original}__{current_variant}
        payload  = data[10:]  # strip "linkagain_"
        if "__" in payload:
            original, account = payload.split("__", 1)
        else:
            original = payload
            account  = payload

        # Cancel any active pairing on the old number
        with pairs_lock:
            for num in (original, account):
                if num in active_pairs:
                    active_pairs[num]["cancelled"] = True

        # Ensure new number row exists in DB with original as reference
        with get_db() as db:
            ex = db.execute("SELECT id FROM numbers WHERE user_id=? AND account=?", (uid, account)).fetchone()
            if ex:
                db.execute(
                    "UPDATE numbers SET status='pairing',pair_code=NULL,wsid=NULL WHERE user_id=? AND account=?",
                    (uid, account)
                )
            else:
                db.execute(
                    "INSERT INTO numbers(user_id,account,status) VALUES(?,?,'pairing')",
                    (uid, account)
                )
            # Store original on the new row so further variants chain correctly
            try:
                db.execute("UPDATE numbers SET pair_code=? WHERE user_id=? AND account=?",
                           (f"orig:{original}", uid, account))
            except Exception:
                pass

        # Pre-set original in active_pairs so _pair_bg picks it up
        with pairs_lock:
            active_pairs[account] = {
                "user_id": uid, "pair_code": None, "status": "pairing",
                "wsid": None, "cancelled": False, "original": original
            }

        next_v = _next_number_variant(original, account)
        await query.edit_message_text(
            f"🔄 Trying `{account}`...\n"
            f"⏳ Pairing code coming shortly.\n"
            f"{'Next variant after this: `' + next_v + '`' if next_v else '⚠️ This is the last variant.'}",
            parse_mode="Markdown"
        )
        threading.Thread(target=_pair_bg, args=(uid, account), daemon=True).start()

# Send All
async def send_all(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return
    mode = get_earning_mode()
    
    if mode == "auto":
        with get_db() as db:
            online = db.execute("SELECT COUNT(*) as c FROM auto_numbers WHERE user_id=? AND status='online'", (uid,)).fetchone()["c"]
            total = db.execute("SELECT COUNT(*) as c FROM auto_numbers WHERE user_id=?", (uid,)).fetchone()["c"]
        await update.message.reply_text(f"Auto mode: {online} of {total} numbers are online and earning automatically. No manual action needed.")
        return
    
    if mode == "wacash":
        with get_db() as db:
            rows = db.execute("SELECT account, ws_id FROM wacash_numbers WHERE user_id=? AND status='online' AND ws_id IS NOT NULL", (uid,)).fetchall()
        if not rows:
            await update.message.reply_text("No online numbers were found. Please connect a number first using *Add Number*.")
            return

        # Initial message (will be edited later)
        msg = await update.message.reply_text("🔄 **Sending messages in batches...**\n⏳ Please wait...", parse_mode="Markdown")

        # Start background task
        async def background_send():
            try:
                threads_per = int(get_setting("wacash_threads", "20"))
                ppm = int(get_setting("points_per_msg", "200"))

                per_num_results = {}
                per_num_lock = threading.Lock()

                # --- fire_until_offline (runs in thread pool) ---
                def fire_until_offline(acct, ws_id):
                    total_success = 0
                    total_failed = 0
                    consecutive_fail_batches = 0

                    while True:
                        batch_results = []
                        batch_lock = threading.Lock()

                        def _fire(wid=ws_id):
                            ok, _ = wacash_send_msg(wid)
                            with batch_lock:
                                batch_results.append(ok)

                        with concurrent.futures.ThreadPoolExecutor(max_workers=threads_per) as ex:
                            concurrent.futures.wait([ex.submit(_fire) for _ in range(threads_per)])

                        batch_success = sum(batch_results)
                        batch_failed = len(batch_results) - batch_success
                        total_success += batch_success
                        total_failed += batch_failed

                        log.info(f"[TaskGo:Fire] {acct} ws_id={ws_id} batch: ok={batch_success} fail={batch_failed}")

                        if batch_success == 0:
                            consecutive_fail_batches += 1
                            if consecutive_fail_batches >= 3:
                                with get_db() as db2:
                                    db2.execute("UPDATE wacash_numbers SET status='offline' WHERE user_id=? AND account=?", (uid, acct))
                                break
                            time.sleep(2)
                        else:
                            consecutive_fail_batches = 0

                    with per_num_lock:
                        per_num_results[acct] = {"success": total_success, "failed": total_failed}

                # --- Blocking fire block (run in executor) ---
                def run_fire_block():
                    with _wacash_fire_lock:
                        task_before = wacash_get_task_info()
                        sends_before = task_before.get("todaySendNum", 0) if task_before else 0

                        with concurrent.futures.ThreadPoolExecutor(max_workers=len(rows)) as ex:
                            concurrent.futures.wait([
                                ex.submit(fire_until_offline, r["account"], r["ws_id"]) for r in rows
                            ])

                        task_after = wacash_get_task_info()
                        sends_after = task_after.get("todaySendNum", 0) if task_after else 0
                        return max(0, sends_after - sends_before), per_num_results

                # Run blocking part in a separate thread
                loop = asyncio.get_running_loop()
                actual_sends, per_num_results = await loop.run_in_executor(None, run_fire_block)

                total_earned_pts = actual_sends * ppm

                if actual_sends > 0:
                    with get_db() as db:
                        _credit(db, uid, total_earned_pts, f"TaskGo: sent {actual_sends} messages")
                        _increment_daily_msgs(db, uid, actual_sends)
                        for r in rows:
                            num_ok = per_num_results.get(r["account"], {}).get("success", 0)
                            if num_ok > 0:
                                db.execute("UPDATE wacash_numbers SET msgs_sent=msgs_sent+? WHERE user_id=? AND account=?", (num_ok, uid, r["account"]))
                        u = db.execute("SELECT referred_by FROM users WHERE id=?", (uid,)).fetchone()
                        if u and u["referred_by"]:
                            bonus = max(1, int(total_earned_pts * float(get_setting("referral_pct", "5")) / 100))
                            _credit(db, u["referred_by"], bonus, f"Ref bonus from uid={uid}", "referral")
                        new_bal = db.execute("SELECT balance FROM users WHERE id=?", (uid,)).fetchone()["balance"]

                    naira_earned = pts_to_ngn(total_earned_pts)
                    final_text = (
                        f"✅ Sent {actual_sends} messages!\n"
                        f"💎 Earned {total_earned_pts:,} pts (≈ ₦{naira_earned:.2f})\n"
                        f"💰 Balance: {new_bal:,} pts"
                    )
                    await msg.edit_text(final_text, parse_mode="Markdown")
                else:
                    await msg.edit_text("⚠️ No messages were delivered. Please verify that your numbers are online and retry.", parse_mode="Markdown")

            except Exception as e:
                log.error(f"Background send_all error: {e}")
                await msg.edit_text(f"❌ An error occurred: {str(e)[:100]}", parse_mode="Markdown")

        # Fire and forget – the handler returns immediately
        asyncio.create_task(background_send())
        await update.message.reply_text("🚀 Sending started in background. You will receive the result here shortly.")
        return
    
    # Manual mode (unchanged, but for completeness)
    with get_db() as db:
        rows = db.execute("SELECT account, wsid FROM numbers WHERE user_id=? AND status='online' AND wsid IS NOT NULL", (uid,)).fetchall()
    if not rows:
        await update.message.reply_text("No online numbers were found. Please connect a number first using *Add Number*.")
        return
    
    msg = await update.message.reply_text("🔄 **Sending messages concurrently...**\n⏳ Please wait...", parse_mode="Markdown")
    npm = float(get_setting("naira_per_msg", "30"))
    ppm = int(get_setting("points_per_msg", "200"))
    results = []
    lock = threading.Lock()
    ready_count = [0]
    total_count = len(rows)
    go_event = threading.Event()
    
    def do(acct, wsid):
        s = _ps()
        uid_str, uname = str(s["userid"]), s["username"]
        sign = _s0("/api/user/sendmsg", uid_str, uname, tx=str(wsid))
        payload = {"phone": acct, "wsid": wsid, "username": uname, "userid": int(uid_str), "sign": sign}
        hdrs = _hdrs()
        with lock:
            ready_count[0] += 1
            if ready_count[0] == total_count:
                go_event.set()
        go_event.wait()
        try:
            r = s["http"].post(f"{BASE_URL}/api/user/sendmsg", json=payload, headers=hdrs, timeout=15)
            d = r.json()
            ok = d.get("code") == 0
        except Exception:
            ok = False
        with lock:
            results.append((acct, ok))
    
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(len(rows), 50)) as ex:
        concurrent.futures.wait([ex.submit(do, r["account"], r["wsid"]) for r in rows])
    
    sent = sum(1 for _,ok in results if ok)
    total_earned_pts = sent * ppm
    
    if sent > 0:
        with get_db() as db:
            _credit(db, uid, total_earned_pts, f"Manual send-all")
            _increment_daily_msgs(db, uid, sent)
            for acct, ok in results:
                if ok:
                    db.execute("UPDATE numbers SET msgs_sent=COALESCE(msgs_sent,0)+1 WHERE user_id=? AND account=?", (uid, acct))
            u = db.execute("SELECT referred_by FROM users WHERE id=?", (uid,)).fetchone()
            if u and u["referred_by"]:
                bonus = max(1, int(total_earned_pts * float(get_setting("referral_pct", "5")) / 100))
                _credit(db, u["referred_by"], bonus, f"Ref bonus from uid={uid}", "referral")
            new_bal = db.execute("SELECT balance FROM users WHERE id=?", (uid,)).fetchone()["balance"]
        await msg.edit_text(f"✅ Sent {sent}/{len(rows)} messages. Earned {total_earned_pts} points.\n💰 New balance: {new_bal:,} pts.")
    else:
        await msg.edit_text("❌ No messages could be sent. Some numbers may be offline.")

# Leaderboard
async def leaderboard(update: Update, context: ContextTypes.DEFAULT_TYPE):
    period = "daily"
    today = datetime.utcnow().strftime("%Y-%m-%d")
    with get_db() as db:
        if period == "daily":
            rows = db.execute(
                "SELECT u.username, COALESCE(dm.msgs_count,0) as msgs_today FROM daily_msgs dm JOIN users u ON dm.user_id=u.id WHERE dm.date=? AND dm.msgs_count>0 ORDER BY dm.msgs_count DESC LIMIT 20",
                (today,)).fetchall()
            total_msgs = db.execute("SELECT COALESCE(SUM(msgs_count),0) as s FROM daily_msgs WHERE date=?", (today,)).fetchone()["s"]
        else:
            rows = []
            total_msgs = 0
    if not rows:
        await update.message.reply_text("No activity today. Send messages to appear on the leaderboard!")
        return
    
    # Build text WITHOUT Markdown special characters that could break parsing
    text = f"🏆 Daily Leaderboard ({today})\n\n"
    for i, r in enumerate(rows, 1):
        username = r["username"]
        # Mask username for privacy
        if len(username) > 4:
            masked_name = username[:2] + "***" + username[-1]
        else:
            masked_name = username
        text += f"{i}. {masked_name} — {r['msgs_today']} msgs\n"
    text += f"\n📊 Total messages today: {total_msgs}"
    
    # Use parse_mode=None to avoid Markdown issues
    await update.message.reply_text(text, parse_mode=None)

# Check-in
async def check_in(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return
    today = datetime.utcnow().strftime("%Y-%m-%d")
    yesterday = (datetime.utcnow() - __import__('datetime').timedelta(days=1)).strftime("%Y-%m-%d")
    with get_db() as db:
        existing = db.execute("SELECT id FROM check_ins WHERE user_id=? AND date=?", (uid, today)).fetchone()
        if existing:
            await update.message.reply_text("You have already checked in today!")
            return
        prev = db.execute("SELECT streak FROM check_ins WHERE user_id=? AND date=?", (uid, yesterday)).fetchone()
        streak = (prev["streak"] + 1) if prev else 1
        pts = min(50 + (streak-1)*10, 150)
        npm = float(get_setting("naira_per_msg", "30"))
        ppm = int(get_setting("points_per_msg", "200"))
        ngn_amt = (pts / ppm * npm) if ppm>0 else 0
        db.execute("INSERT INTO check_ins(user_id,date,points_awarded,streak) VALUES(?,?,?,?)", (uid, today, pts, streak))
        _credit(db, uid, int(ngn_amt), f"Daily check-in bonus (Day {streak})", "checkin")
        await update.message.reply_text(f"🎉 Check-in successful! Day {streak} streak.\nYou earned {pts} points!")
        await send_telegram(telegram_id, f"🎉 Daily check-in bonus! +{pts} pts. Keep it up!")

# Withdraw conversation
async def withdraw_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Choose withdrawal method:",
                                    reply_markup=InlineKeyboardMarkup([
                                        [InlineKeyboardButton("🏦 Bank Transfer", callback_data="with_bank")],
                                        [InlineKeyboardButton("💎 TRX (USDT)", callback_data="with_trx")]
                                    ]))
    return SELECTING_WITHDRAW_METHOD

async def withdraw_method_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    method = query.data.split("_")[1]
    context.user_data["withdraw_method"] = method
    await query.edit_message_text(f"Selected: {method.upper()}\n\nPlease send the amount in POINTS (minimum {get_setting('min_withdrawal','15000')} pts):\nSend /cancel to abort.")
    return TYPING_AMOUNT

async def withdraw_amount_receive(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return ConversationHandler.END
    try:
        amount = int(update.message.text.strip())
    except:
        await update.message.reply_text("Invalid amount. Please enter a number.")
        return TYPING_AMOUNT
    min_pts = int(get_setting("min_withdrawal", "15000"))
    if amount < min_pts:
        await update.message.reply_text(f"Minimum withdrawal is {min_pts} points.")
        return TYPING_AMOUNT
    with get_db() as db:
        bal = db.execute("SELECT balance FROM users WHERE id=?", (uid,)).fetchone()["balance"]
    if amount > bal:
        await update.message.reply_text("Insufficient balance.")
        return TYPING_AMOUNT
    context.user_data["withdraw_amount"] = amount
    await update.message.reply_text("Please enter your account password to confirm withdrawal:")
    return TYPING_PASSWORD

async def withdraw_password_receive(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return ConversationHandler.END
    password = update.message.text.strip()
    with get_db() as db:
        user = db.execute("SELECT password FROM users WHERE id=?", (uid,)).fetchone()
        if not _verify_pw(password, user["password"]):
            await update.message.reply_text("Incorrect password. Withdrawal cancelled.")
            return ConversationHandler.END
    method = context.user_data["withdraw_method"]
    amount = context.user_data["withdraw_amount"]
    npm = float(get_setting("naira_per_msg", "30"))
    ppm = int(get_setting("points_per_msg", "200"))
    ngn_payout = (amount / ppm * npm) if ppm>0 else 0
    handling_fee_pts = 200
    total_deduct = amount + handling_fee_pts
    with get_db() as db:
        bal = db.execute("SELECT balance FROM users WHERE id=?", (uid,)).fetchone()["balance"]
        if total_deduct > bal:
            await update.message.reply_text("Insufficient balance after including handling fee.")
            return ConversationHandler.END
        _debit(db, uid, total_deduct, "Withdrawal")
        if method == "bank":
            bank = db.execute("SELECT * FROM bank_details WHERE user_id=?", (uid,)).fetchone()
            if not bank:
                await update.message.reply_text("No bank details found. Please set them in Settings first.")
                return ConversationHandler.END
            db.execute("INSERT INTO withdrawals(user_id,amount,method,status,bank_name,account_num,account_name,pts_amount) VALUES(?,?,?,'pending',?,?,?,?)",
                       (uid, ngn_payout, method, bank["bank_name"], bank["account_num"], bank["account_name"], amount))
        else:  # trx
            wallet = db.execute("SELECT wallet_address FROM trx_wallets WHERE user_id=?", (uid,)).fetchone()
            if not wallet:
                await update.message.reply_text("No TRX wallet set. Please set it in Settings first.")
                return ConversationHandler.END
            db.execute("INSERT INTO withdrawals(user_id,amount,method,status,wallet_addr,pts_amount) VALUES(?,?,?,'pending',?,?)",
                       (uid, ngn_payout, method, wallet["wallet_address"], amount))
    await update.message.reply_text(f"✅ Withdrawal request submitted for {amount} points (≈ ₦{ngn_payout:.2f}).\n"
                                    f"Processing may take 1-3 business days.\n"
                                    f"A handling fee of 200 points was deducted.")
    return ConversationHandler.END

# Referral tree
async def referral(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return
    with get_db() as db:
        u = db.execute("SELECT referral_code FROM users WHERE id=?", (uid,)).fetchone()
        direct = db.execute("SELECT username, created_at FROM users WHERE referred_by=?", (uid,)).fetchall()
        commission = db.execute("SELECT COALESCE(SUM(amount),0) as s FROM transactions WHERE user_id=? AND type='referral'", (uid,)).fetchone()["s"]
    text = f"🔗 *Your Referral Link*\n`https://t.me/{context.bot.username}?start=ref_{u['referral_code']}`\n\n"
    text += f"👥 Direct referrals: {len(direct)}\n"
    text += f"💰 Total commission earned: {int(commission):,} points\n\n"
    if direct:
        text += "*Recent referrals:*\n"
        for d in direct[:10]:
            text += f"• {d['username']} (joined {d['created_at'][:10]})\n"
    await update.message.reply_text(text, parse_mode="Markdown")
    
async def hourly_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show user's hourly earning status for all their numbers"""
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return

    # First, check if user is in hourly mode
    with get_db() as db:
        user = db.execute("SELECT earning_mode FROM users WHERE id=?", (uid,)).fetchone()
        user_mode = user["earning_mode"] if user else "manual"
    
    if user_mode != "hourly":
        await update.message.reply_text(
            "⚠️ You are not in Hourly Mode!\n\n"
            "To switch to Hourly Mode, use the Settings menu or contact an admin.\n\n"
            "Current mode: " + user_mode,
            parse_mode="Markdown"
        )
        return

    with get_db() as db:
        numbers = db.execute("""
            SELECT account, hourly_status, hourly_start_time, total_hours_earned, msgs_sent, status
            FROM numbers
            WHERE user_id = ?
            ORDER BY added_at DESC
        """, (uid,)).fetchall()

    if not numbers:
        await update.message.reply_text(
            "📱 *No Hourly Numbers Found*\n\n"
            "Use *➕ Add Number* to connect your first WhatsApp number in Hourly Mode!\n\n"
            "Once connected, you'll earn ₦5 per hour automatically.",
            parse_mode="Markdown"
        )
        return

    # Get current rate
    rate_ngn = float(get_setting("hourly_rate_ngn", "5.0"))
    
    text = "⚡ *HOURLY EARNING STATUS*\n"
    text += "━━━━━━━━━━━━━━━━━━━━\n\n"
    
    total_earned_ngn = 0
    active_count = 0
    offline_count = 0
    pending_count = 0
    
    for num in numbers:
        status = num["hourly_status"] or "pending"
        account = num["account"]
        total_hours = num["total_hours_earned"] or 0
        earned_ngn = total_hours * rate_ngn
        total_earned_ngn += earned_ngn
        pairing_status = num["status"]
        
        if status == "online":
            active_count += 1
            emoji = "🟢"
            status_text = "ONLINE"
            # Calculate current session hours
            start_time = num["hourly_start_time"]
            if start_time:
                try:
                    start = datetime.fromisoformat(start_time.replace(' ', 'T'))
                    now = datetime.utcnow()
                    session_hours = int((now - start).total_seconds() / 3600)
                    status_text += f" · {session_hours} hrs this session"
                except:
                    pass
        elif status == "offline":
            offline_count += 1
            emoji = "🔴"
            status_text = "OFFLINE"
            if pairing_status == "pairing":
                status_text = "PENDING PAIRING"
                emoji = "🟡"
        else:
            pending_count += 1
            emoji = "🟡"
            status_text = "PENDING"
        
        text += f"{emoji} `{account}`\n"
        text += f"   └ Status: {status_text}\n"
        if total_hours > 0:
            text += f"   └ Total earned: ₦{earned_ngn:.2f} ({total_hours} hours)\n"
        text += "\n"
    
    text += "━━━━━━━━━━━━━━━━━━━━\n"
    text += f"📊 *Summary*\n"
    text += f"🟢 Active (online): {active_count}\n"
    text += f"🔴 Offline: {offline_count}\n"
    text += f"🟡 Pending: {pending_count}\n"
    text += f"💰 Total hourly earnings: ₦{total_earned_ngn:.2f}\n"
    text += f"⚡ Current rate: ₦{rate_ngn}/hour\n\n"
    text += "_Keep your numbers online to earn continuously!_\n\n"
    text += "💡 *Tip:* Numbers appear as 'PENDING' until you complete WhatsApp pairing."
    
    await update.message.reply_text(text, parse_mode="Markdown")

# Settings (change password, set bank/trx)
async def settings_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    
    with get_db() as db:
        current_mode = db.execute("SELECT earning_mode FROM users WHERE id=?", (uid,)).fetchone()
        current_mode = current_mode["earning_mode"] if current_mode else "manual"
    
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("🔄 Change Earning Mode", callback_data="sett_change_mode")],
        [InlineKeyboardButton("🔐 Change Password", callback_data="sett_password")],
        [InlineKeyboardButton("🏦 Set Bank Details", callback_data="sett_bank")],
        [InlineKeyboardButton("💎 Set TRX Wallet", callback_data="sett_trx")],
        [InlineKeyboardButton("🔙 Back", callback_data="sett_back")]
    ])
    await update.message.reply_text(
        f"⚙️ *Settings*\n\n"
        f"Current earning mode: *{current_mode.upper()}*\n\n"
        f"Select an option:",
        reply_markup=keyboard, 
        parse_mode="Markdown"
    )

async def settings_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data = query.data
    
    if data == "sett_change_mode":
        keyboard = InlineKeyboardMarkup([
            [InlineKeyboardButton("💰 Manual Mode", callback_data="set_mode_manual")],
            [InlineKeyboardButton("⚡ Hourly Mode", callback_data="set_mode_hourly")],
            [InlineKeyboardButton("🔙 Back to Settings", callback_data="sett_back")]
        ])
        await query.edit_message_text(
            "🔄 *Change Your Earning Mode*\n\n"
            "Choose your preferred earning method:\n\n"
            "💰 *Manual Mode* – You press 'Send All' to earn points\n"
            "⚡ *Hourly Mode* – Earn ₦5 per hour automatically\n\n"
            "⚠️ Note: Changing mode will affect new numbers you add.\n"
            "Existing numbers will keep their current mode.",
            reply_markup=keyboard,
            parse_mode="Markdown"
        )
        return
    
    elif data == "sett_password":
        await query.edit_message_text("Send your new password (min 6 characters).\nSend /cancel to abort.")
        context.user_data["setting_action"] = "password"
        return
    
    elif data == "sett_bank":
        await query.edit_message_text("Send bank details in format:\n`Account Number, Account Name, Bank Name`\nExample: `1234567890, John Doe, GTBank`")
        context.user_data["setting_action"] = "bank"
        return
    
    elif data == "sett_trx":
        await query.edit_message_text("Send your TRC20 wallet address (starts with T, 34 chars):")
        context.user_data["setting_action"] = "trx"
        return
    
    elif data == "sett_back":
        await query.edit_message_text("Settings closed.", reply_markup=main_keyboard)
        return

async def handle_settings_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    action = context.user_data.get("setting_action")
    if not action:
        return
    telegram_id = update.effective_user.id
    uid = get_internal_user_id(telegram_id)
    if not uid:
        await update.message.reply_text("Please use /start to register before proceeding.")
        return
    if action == "password":
        new_pw = update.message.text.strip()
        if len(new_pw) < 6:
            await update.message.reply_text("Password must be at least 6 characters.")
            return
        with get_db() as db:
            db.execute("UPDATE users SET password=? WHERE id=?", (_hash_pw(new_pw), uid))
        await update.message.reply_text("✅ Password changed successfully.")
    elif action == "bank":
        parts = update.message.text.split(',')
        if len(parts) != 3:
            await update.message.reply_text("Invalid format. Please use: Account Number, Account Name, Bank Name")
            return
        acc_num, acc_name, bank_name = [p.strip() for p in parts]
        if not acc_num.isdigit() or len(acc_num) < 10:
            await update.message.reply_text("Invalid account number.")
            return
        with get_db() as db:
            db.execute("INSERT OR REPLACE INTO bank_details(user_id,account_num,account_name,bank_name) VALUES(?,?,?,?)",
                       (uid, acc_num, acc_name, bank_name))
        await update.message.reply_text("✅ Bank details saved.")
    elif action == "trx":
        addr = update.message.text.strip()
        if not (addr.startswith("T") and len(addr) == 34 and addr.isalnum()):
            await update.message.reply_text("Invalid TRC20 address. Must start with T and be 34 alphanumeric chars.")
            return
        with get_db() as db:
            db.execute("INSERT OR REPLACE INTO trx_wallets(user_id,wallet_address) VALUES(?,?)", (uid, addr))
        await update.message.reply_text("✅ TRX wallet saved.")
    elif action == "manual_creds":
        parts = update.message.text.strip().split(None, 1)
        if len(parts) != 2:
            await update.message.reply_text(
                "❌ Invalid format. Send: `username password`\nExample: `Frankhustle f11111`",
                parse_mode="Markdown"
            )
            return
        new_user, new_pass = parts[0].strip(), parts[1].strip()
        if not new_user or not new_pass:
            await update.message.reply_text("❌ Both username and password are required.")
            return

        # Update the global variables
        global PLATFORM_USER, PLATFORM_PASS
        PLATFORM_USER = new_user
        PLATFORM_PASS = new_pass

        # Clear old session so it re-logs in fresh
        with platform_lock:
            platform_session.clear()

        # Test the new credentials immediately
        wait_msg = await update.message.reply_text(
            f"⏳ Testing new credentials for `{new_user}`...",
            parse_mode="Markdown"
        )
        loop = asyncio.get_event_loop()
        ok = await loop.run_in_executor(None, platform_login)
        if ok:
            with platform_lock:
                uid_on_platform = platform_session.get("userid", "?")
            await wait_msg.edit_text(
                f"✅ *Credentials Updated & Login Successful!*\n\n"
                f"👤 Username: `{new_user}`\n"
                f"🆔 Platform UID: `{uid_on_platform}`\n\n"
                f"Manual mode is ready to use.",
                parse_mode="Markdown"
            )
        else:
            await wait_msg.edit_text(
                f"⚠️ *Credentials saved but login failed!*\n\n"
                f"👤 Username: `{new_user}`\n\n"
                f"Please check the username/password and try again.\n"
                f"Use '🧪 Test Manual Login' to retry.",
                parse_mode="Markdown"
            )
        context.user_data.pop("setting_action", None)
        return

    elif action == "wacash_creds":
        parts = update.message.text.strip().split()
        if len(parts) != 2:
            await update.message.reply_text("Invalid format. Send: `phone_number password`")
            return
        phone, pwd = parts[0].strip(), parts[1].strip()
        if not phone or not pwd:
            await update.message.reply_text("Both phone and password are required.")
            return
        with get_db() as db:
            db.execute("INSERT OR REPLACE INTO settings(key, value) VALUES('wacash_account', ?)", (phone,))
            db.execute("INSERT OR REPLACE INTO settings(key, value) VALUES('wacash_password', ?)", (pwd,))
        if wacash_login():
            await update.message.reply_text("✅ Wacash credentials saved and login successful!")
        else:
            await update.message.reply_text("⚠️ Credentials saved but login failed. Please check the account/password.")
        context.user_data.pop("setting_action", None)
        await settings_menu(update, context)
        return
    elif action == "wacash_threads":
        try:
            threads = int(update.message.text.strip())
            threads = max(1, min(threads, 100))
            set_setting("wacash_threads", str(threads))
            await update.message.reply_text(f"✅ Wacash threads set to {threads} per batch.\n\nEach number will send {threads} concurrent requests per batch until offline.")
        except ValueError:
            await update.message.reply_text("❌ Invalid number. Please send a number between 1 and 100.")
        context.user_data.pop("setting_action", None)
        await settings_menu(update, context)
        return
    elif action == "points_per_msg":
        try:
            points = int(update.message.text.strip())
            if points < 1:
                await update.message.reply_text("Points must be at least 1.")
                return
            set_setting("points_per_msg", str(points))
            await update.message.reply_text(f"✅ Points per message set to **{points}** points.\n\nUsers will now earn {points} points per message sent.\n⚠️ Existing balances remain unchanged.")
        except ValueError:
            await update.message.reply_text("❌ Invalid number. Please send a valid number.")
        context.user_data.pop("setting_action", None)
        await settings_menu(update, context)
        return
    elif action == "naira_per_msg":
        try:
            naira = float(update.message.text.strip())
            if naira < 0.01:
                await update.message.reply_text("Naira value must be at least 0.01.")
                return
            set_setting("naira_per_msg", str(naira))
            await update.message.reply_text(f"✅ Naira per point set to **₦{naira}**.\n\n1 point = ₦{naira}\n⚠️ Existing balances remain unchanged.\n\n*Example:* 200 points = ₦{200 * naira:.2f}", parse_mode="Markdown")
        except ValueError:
            await update.message.reply_text("❌ Invalid number. Please send a valid number.")
        context.user_data.pop("setting_action", None)
        await settings_menu(update, context)
        return
    
    # ========== HOURLY ADMIN INPUT HANDLERS ==========
    elif action == "admin_hourly_rate":
        try:
            rate = float(update.message.text.strip())
            if rate <= 0:
                raise ValueError
            set_setting("hourly_rate_ngn", str(rate))
            await update.message.reply_text(
                f"✅ Hourly rate set to **₦{rate}** per hour.\n\nNew earnings will use this rate.",
                parse_mode="Markdown"
            )
        except ValueError:
            await update.message.reply_text(
                "❌ Invalid amount. Please send a positive number (e.g., `10`).",
                parse_mode="Markdown"
            )
        context.user_data.pop("setting_action", None)
        await settings_menu(update, context)
        return

    elif action == "admin_hourly_interval":
        parts = update.message.text.strip().split()
        if len(parts) != 2:
            await update.message.reply_text(
                "❌ Please send two numbers: `<monitor_seconds> <payout_minutes>`\nExample: `60 60`",
                parse_mode="Markdown"
            )
            return
        try:
            monitor_sec = int(parts[0])
            payout_min = int(parts[1])
            if monitor_sec < 10 or payout_min < 1:
                raise ValueError
            set_setting("hourly_monitor_interval_seconds", str(monitor_sec))
            set_setting("hourly_payout_interval_minutes", str(payout_min))
            await update.message.reply_text(
                f"✅ Intervals updated!\n\n"
                f"• Monitor interval: {monitor_sec} seconds\n"
                f"• Payout interval: {payout_min} minutes\n\n"
                f"Changes will take effect on next cycle.",
                parse_mode="Markdown"
            )
        except ValueError:
            await update.message.reply_text(
                "❌ Invalid numbers. Monitor ≥ 10 seconds, Payout ≥ 1 minute.",
                parse_mode="Markdown"
            )
        context.user_data.pop("setting_action", None)
        await settings_menu(update, context)
        return
    # ===============================================

    context.user_data.pop("setting_action", None)
    await settings_menu(update, context)

# ----------------------------------------------------------------------
# Admin Panel Handlers (callbacks)
# ----------------------------------------------------------------------
async def admin_panel_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data = query.data
    telegram_id = update.effective_user.id
    if telegram_id != ADMIN_TELEGRAM_ID:
        await query.edit_message_text("You are not authorized to use admin panel.")
        return

    if data == "admin_stats":
        with get_db() as db:
            total_users = db.execute("SELECT COUNT(*) as c FROM users").fetchone()["c"]
            total_numbers = db.execute("SELECT COUNT(*) as c FROM numbers").fetchone()["c"] + \
                            db.execute("SELECT COUNT(*) as c FROM auto_numbers").fetchone()["c"]
            pending_wd = db.execute("SELECT COUNT(*) as c FROM withdrawals WHERE status='pending'").fetchone()["c"]
            total_bal = db.execute("SELECT COALESCE(SUM(balance),0) as s FROM users").fetchone()["s"]
            mode = get_earning_mode()
            rev_today = db.execute("SELECT COALESCE(SUM(amount),0) as s FROM transactions WHERE type='earn' AND date(created_at)=date('now')").fetchone()["s"]
        text = (
            f"📊 *Admin Stats*\n"
            f"👥 Users: {total_users}\n"
            f"📞 Numbers: {total_numbers}\n"
            f"⏳ Pending withdrawals: {pending_wd}\n"
            f"💰 Total balance: {total_bal:,.2f} NGN\n"
            f"🔄 Earning mode: {mode}\n"
            f"📈 Revenue today: {rev_today:,.2f} NGN"
        )
        await query.edit_message_text(text, parse_mode="Markdown", reply_markup=admin_panel_markup)

    elif data == "admin_users":
        with get_db() as db:
            rows = db.execute("SELECT id, username, telegram_id, balance, is_banned, created_at FROM users ORDER BY created_at DESC LIMIT 20").fetchall()
        text = "*Recent Users*\n\n"
        for r in rows:
            ban = "🚫" if r["is_banned"] else "✅"
            text += f"{ban} `{r['username']}` – bal: {r['balance']:.0f} pts\n"
        await query.edit_message_text(text, parse_mode="Markdown", reply_markup=admin_panel_markup)

    elif data == "admin_withdrawals":
        with get_db() as db:
            wds = db.execute("SELECT w.id, u.username, w.amount, w.method, w.status, w.created_at FROM withdrawals w JOIN users u ON w.user_id=u.id WHERE w.status='pending' ORDER BY w.created_at ASC").fetchall()
        if not wds:
            await query.edit_message_text("No pending withdrawals.", reply_markup=admin_panel_markup)
            return
        text = "⏳ *Pending Withdrawals*\n\n"
        for w in wds:
            text += f"ID: `{w['id']}` | {w['username']} | ₦{w['amount']:.2f} | {w['method']} | {w['created_at'][:10]}\n"
        text += "\nTo approve/reject, use:\n/admin_withdraw <id> approve|reject [reason]"
        await query.edit_message_text(text, parse_mode="Markdown", reply_markup=admin_panel_markup)

    elif data == "admin_credit":
        await query.edit_message_text("Send the command: `/credit_user <user_id> <points>`\n(You can get user_id from /admin_users)",
                                      parse_mode="Markdown")

    elif data == "admin_ban":
        await query.edit_message_text("Send the command: `/ban_user <user_id>` to toggle ban status.\nUse `/admin_users` to get user_id.")

    elif data == "admin_mode":
        keyboard = InlineKeyboardMarkup([
            [InlineKeyboardButton("⚙️ Manual Mode", callback_data="earn_manual")],
            [InlineKeyboardButton("🤖 Auto Mode", callback_data="earn_auto")],
            [InlineKeyboardButton("📲 Wacash Mode", callback_data="earn_wacash")],
            [InlineKeyboardButton("🔙 Back", callback_data="admin_back")]
        ])
        await query.edit_message_text("Select earning mode:", reply_markup=keyboard)

    elif data == "admin_set_manual_creds":
        current_user = PLATFORM_USER
        await query.edit_message_text(
            f"🔐 *Set Manual Mode Login Credentials*\n\n"
            f"Current username: `{current_user}`\n\n"
            f"Send new credentials in format:\n"
            f"`username password`\n\n"
            f"Example: `Frankhustle f11111`\n"
            f"Send /cancel to abort.",
            parse_mode="Markdown"
        )
        context.user_data["setting_action"] = "manual_creds"
        return

    elif data == "admin_test_manual_login":
        await query.edit_message_text(
            f"🧪 Testing manual mode login with current credentials...\n"
            f"Username: `{PLATFORM_USER}`",
            parse_mode="Markdown"
        )
        loop = asyncio.get_event_loop()
        ok = await loop.run_in_executor(None, platform_login)
        if ok:
            with platform_lock:
                uid_on_platform = platform_session.get("userid", "?")
            await query.edit_message_text(
                f"✅ *Login Test Successful!*\n\n"
                f"👤 Username: `{PLATFORM_USER}`\n"
                f"🆔 Platform UID: `{uid_on_platform}`\n"
                f"🌐 Base URL: `{BASE_URL}`\n\n"
                f"Manual mode is ready to use.",
                parse_mode="Markdown",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("◀️ Back to Admin Panel", callback_data="admin_back")
                ]])
            )
        else:
            await query.edit_message_text(
                f"❌ *Login Test Failed!*\n\n"
                f"👤 Username: `{PLATFORM_USER}`\n"
                f"🌐 Base URL: `{BASE_URL}`\n\n"
                f"Please update credentials using\n"
                f"'🔐 Set Manual Login Creds' and try again.",
                parse_mode="Markdown",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("🔐 Update Credentials", callback_data="admin_set_manual_creds"),
                    InlineKeyboardButton("◀️ Back", callback_data="admin_back")
                ]])
            )
        return

    elif data == "admin_set_wacash":
        await query.edit_message_text(
            "Send the WorkGo1 **phone number** and **password** separated by a space:\n"
            "`<phone> <password>`\n\n"
            "Example: `08012345678 MySecret123`\n"
            "Send /cancel to abort."
        )
        context.user_data["setting_action"] = "wacash_creds"
        return

    elif data == "admin_set_threads":
        await query.edit_message_text(
            "Send the number of concurrent requests per batch for Wacash mode:\n"
            "`<threads>`\n\n"
            "Example: `20` (default)\n"
            "Higher = more messages per batch but may get rate limited.\n"
            "Range: 1-100",
            parse_mode="Markdown"
        )
        context.user_data["setting_action"] = "wacash_threads"
        return

    elif data == "admin_points_per_msg":
        current = get_setting("points_per_msg", "200")
        await query.edit_message_text(
            f"Send the number of **points** earned per message sent:\n"
            f"`<points>`\n\n"
            f"Example: `200` (default)\n"
            f"Current value: `{current}`",
            parse_mode="Markdown"
        )
        context.user_data["setting_action"] = "points_per_msg"
        return

    elif data == "admin_naira_per_msg":
        current = get_setting("naira_per_msg", "30")
        await query.edit_message_text(
            f"Send the **naira value** per point (1 point = ? NGN):\n"
            f"`<naira>`\n\n"
            f"Example: `0.15` means 1 point = ₦0.15\n"
            f"Current value: `{current}`",
            parse_mode="Markdown"
        )
        context.user_data["setting_action"] = "naira_per_msg"
        return

    elif data.startswith("earn_"):
        log.info(f"🔁 Mode switch callback received: {data}")
        new_mode = data.split("_")[1]
        log.info(f"🔁 Switching to mode: {new_mode}")
        
        # If switching to wacash, verify credentials exist
        if new_mode == "wacash":
            acct = get_setting("wacash_account", "")
            pwd = get_setting("wacash_password", "")
            log.info(f"Wacash credentials - Account: {'SET' if acct else 'NOT SET'}, Password: {'SET' if pwd else 'NOT SET'}")
            if not acct or not pwd:
                await query.edit_message_text(
                    "⚠️ Cannot switch to Wacash mode: No WorkGo1 credentials set.\n"
                    "Please set them using '🔑 Set Wacash Credentials' first.",
                    reply_markup=admin_panel_markup
                )
                return
        
        # Direct database update to ensure it works
        with get_db() as db:
            db.execute("INSERT OR REPLACE INTO settings(key, value) VALUES('earning_mode', ?)", (new_mode,))
        
        # Also update via set_setting for cache
        set_setting("earning_mode", new_mode)
        
        # Verify the update worked
        with get_db() as db:
            verify = db.execute("SELECT value FROM settings WHERE key='earning_mode'").fetchone()
            log.info(f"Verified mode in DB: {verify['value'] if verify else 'NOT FOUND'}")
        
        # Post-switch side effects
        if new_mode == "wacash":
            threading.Thread(target=wacash_login, daemon=True).start()
        elif new_mode == "auto" and _worker_client is None:
            asyncio.create_task(_start_task_worker())

        # Verify the switch actually took effect by reading back from DB
        confirmed = get_earning_mode()
        mode_notes = {
            "manual": "Users must tap Send All to fire messages manually.",
            "auto":   "Telethon worker will auto-pair and send for each user.",
            "wacash": "WorkGo1 (TaskGo) handles pairing and message sending.",
        }
        mode_icons = {"manual": "\U0001f590", "auto": "\U0001f916", "wacash": "\U0001f4f2"}

        if confirmed == new_mode:
            feedback = (
                f"{mode_icons.get(new_mode, '⚙️')} *Mode switched to {new_mode.upper()}*\n\n"
                f"✅ Change confirmed in database.\n"
                f"📝 {mode_notes.get(new_mode, '')}"
            )
        else:
            feedback = (
                f"⚠️ *Mode switch may have failed!*\n\n"
                f"Requested: `{new_mode}`\n"
                f"Current in DB: `{confirmed}`\n\n"
                f"Try: `/force_mode {new_mode}`"
            )

        await query.edit_message_text(
            feedback,
            parse_mode="Markdown",
            reply_markup=InlineKeyboardMarkup([[
                InlineKeyboardButton("◀️ Back to Admin Panel", callback_data="admin_back")
            ]])
        )
        log.info(f"Admin switched earning mode to {new_mode} — confirmed={confirmed}")

    elif data == "admin_gen_code":
        await query.edit_message_text("Send command: `/gen_code <points> [count]`\nExample: `/gen_code 500 5`")

    elif data == "admin_broadcast":
        await query.edit_message_text("Send the broadcast message as a reply to this command:\nUse /broadcast Your message here")

    # ========== HOURLY ADMIN CONTROLS ==========
    elif data == "admin_hourly_rate":
        current_rate = get_setting("hourly_rate_ngn", "5.0")
        await query.edit_message_text(
            f"💰 *Set Hourly Rate*\n\n"
            f"Send the new hourly rate in NGN.\n"
            f"Example: `10` for ₦10 per hour\n\n"
            f"Current rate: ₦{current_rate} per hour\n\n"
            f"Send /cancel to abort.",
            parse_mode="Markdown"
        )
        context.user_data["setting_action"] = "admin_hourly_rate"
        return

    elif data == "admin_hourly_interval":
        current_monitor = get_setting("hourly_monitor_interval_seconds", "60")
        current_payout = get_setting("hourly_payout_interval_minutes", "60")
        await query.edit_message_text(
            f"⏱ *Set Hourly Intervals*\n\n"
            f"Send two numbers separated by space:\n"
            f"`<monitor_seconds> <payout_minutes>`\n\n"
            f"Example: `60 60`\n\n"
            f"Current values:\n"
            f"• Monitor interval: {current_monitor} seconds\n"
            f"• Payout interval: {current_payout} minutes\n\n"
            f"Send /cancel to abort.",
            parse_mode="Markdown"
        )
        context.user_data["setting_action"] = "admin_hourly_interval"
        return

    elif data == "admin_hourly_stats":
        with get_db() as db:
            # Total hourly earnings
            total_points = db.execute(
                "SELECT COALESCE(SUM(amount),0) FROM transactions WHERE type='earn' AND description LIKE 'Hourly earning%'"
            ).fetchone()[0]
            total_ngn = pts_to_ngn(total_points)
            
            # Active hourly users
            hourly_users = db.execute(
                "SELECT COUNT(*) FROM users WHERE earning_mode = 'hourly'"
            ).fetchone()[0]
            
            # Online numbers (hourly mode)
            online_numbers = db.execute(
                "SELECT COUNT(*) FROM numbers WHERE hourly_status = 'online'"
            ).fetchone()[0]
            
            # Total numbers in hourly mode
            total_hourly_numbers = db.execute(
                "SELECT COUNT(*) FROM numbers n JOIN users u ON n.user_id = u.id WHERE u.earning_mode = 'hourly'"
            ).fetchone()[0]
            
            rate = get_setting("hourly_rate_ngn", "5.0")
            
        text = (
            f"📊 *Hourly Earnings Stats*\n\n"
            f"💰 Total paid: {int(total_points):,} pts (≈ ₦{total_ngn:.2f})\n"
            f"👥 Users in hourly mode: {hourly_users}\n"
            f"📞 Numbers online: {online_numbers}/{total_hourly_numbers}\n"
            f"⚡ Current rate: ₦{rate}/hour\n\n"
            f"📈 *Tips:*\n"
            f"• Higher rate = more user earnings\n"
            f"• Monitor interval: checks online/offline status\n"
            f"• Payout interval: when users get paid"
        )
        await query.edit_message_text(text, parse_mode="Markdown", reply_markup=admin_panel_markup)

    elif data == "admin_force_hourly":
        await query.edit_message_text(
            "🔄 *Force Hourly Check*\n\n"
            "Triggering immediate hourly payout check for all online numbers...",
            parse_mode="Markdown"
        )
        # Run payout check in background
        asyncio.create_task(force_hourly_payout())
        await asyncio.sleep(2)
        await query.message.reply_text("✅ Hourly payout check triggered successfully!")
    # ==========================================

    elif data == "admin_export":
        with get_db() as db:
            tables = ["users", "transactions", "withdrawals", "numbers", "auto_numbers", "wacash_numbers",
                      "bank_details", "trx_wallets", "settings", "notifications", "claim_codes", "daily_msgs",
                      "check_ins", "admin_logs", "pending_tasks"]
            export = {}
            for tbl in tables:
                rows = db.execute(f"SELECT * FROM {tbl}").fetchall()
                export[tbl] = [dict(r) for r in rows]
        import json, io
        json_str = json.dumps(export, indent=2, default=str)
        file = io.BytesIO(json_str.encode())
        await query.edit_message_text("Exporting data...")
        await context.bot.send_document(chat_id=telegram_id, document=InputFile(file, filename="earnplus_export.json"))
        await query.message.reply_text("Export complete.", reply_markup=admin_panel_markup)

    elif data == "admin_import":
        await query.edit_message_text("Send the JSON backup file as a document. The bot will import it.")

    elif data == "admin_logs":
        with get_db() as db:
            logs = db.execute("SELECT l.*, u.username as admin_name FROM admin_logs l LEFT JOIN users u ON l.admin_id=u.id ORDER BY l.created_at DESC LIMIT 30").fetchall()
        if not logs:
            await query.edit_message_text("No logs found.", reply_markup=admin_panel_markup)
            return
        text = "*Recent Admin Logs*\n\n"
        for l in logs:
            text += f"`{l['created_at'][:16]}` {l['admin_name']}: {l['action']} {l.get('target','')}\n"
        await query.edit_message_text(text, parse_mode="Markdown", reply_markup=admin_panel_markup)

    elif data == "admin_back":
        await query.edit_message_text("Switching back to user menu...")
        await update.effective_chat.send_message("Main menu:", reply_markup=main_keyboard)

async def admin_command_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    text = update.message.text
    if text.startswith("/credit_user"):
        parts = text.split()
        if len(parts) != 3:
            await update.message.reply_text("Usage: /credit_user <user_id> <points>")
            return
        _, uid_str, pts_str = parts
        try:
            uid = int(uid_str)
            pts = int(pts_str)
        except:
            await update.message.reply_text("Invalid numbers.")
            return
        with get_db() as db:
            _credit(db, uid, pts, "Admin credit")
            _admin_log(db, get_internal_user_id(ADMIN_TELEGRAM_ID), "credit_user", f"user_id={uid}", pts)
        await update.message.reply_text(f"Credited {pts} points to user {uid}.")
    elif text.startswith("/ban_user"):
        parts = text.split()
        if len(parts) != 2:
            await update.message.reply_text("Usage: /ban_user <user_id>")
            return
        uid = int(parts[1])
        with get_db() as db:
            user = db.execute("SELECT is_banned FROM users WHERE id=?", (uid,)).fetchone()
            new_ban = 0 if user["is_banned"] else 1
            db.execute("UPDATE users SET is_banned=? WHERE id=?", (new_ban, uid))
            _admin_log(db, get_internal_user_id(ADMIN_TELEGRAM_ID), "ban_user", f"user_id={uid}", f"set to {new_ban}")
        await update.message.reply_text(f"User {uid} ban status updated to {'banned' if new_ban else 'unbanned'}.")
    elif text.startswith("/gen_code"):
        parts = text.split()
        if len(parts) < 2:
            await update.message.reply_text("Usage: /gen_code <points> [count]")
            return
        points = float(parts[1])
        count = int(parts[2]) if len(parts) > 2 else 1
        codes = []
        with get_db() as db:
            for _ in range(count):
                code = f"EARN-{secrets.token_hex(3).upper()}-{secrets.token_hex(3).upper()}"
                db.execute("INSERT INTO claim_codes(code,points) VALUES(?,?)", (code, points))
                codes.append(code)
        await update.message.reply_text(f"Generated {count} code(s) for {points} points each:\n" + "\n".join(codes))
    elif text.startswith("/broadcast"):
        msg = text.replace("/broadcast", "").strip()
        if not msg:
            await update.message.reply_text("Usage: /broadcast <message>")
            return
        with get_db() as db:
            users = db.execute("SELECT telegram_id FROM users WHERE is_banned=0 AND telegram_id IS NOT NULL").fetchall()
        sent = 0
        for u in users:
            try:
                await context.bot.send_message(chat_id=u["telegram_id"], text=f"📢 *Announcement*\n{msg}", parse_mode="Markdown")
                sent += 1
            except Exception as e:
                log.error(f"Broadcast failed to {u['telegram_id']}: {e}")
        await update.message.reply_text(f"Broadcast sent to {sent} users.")
    elif text.startswith("/admin_withdraw"):
        parts = text.split()
        if len(parts) < 3:
            await update.message.reply_text("Usage: /admin_withdraw <withdrawal_id> approve|reject [reason]")
            return
        wd_id = int(parts[1])
        action = parts[2].lower()
        reason = " ".join(parts[3:]) if len(parts)>3 else None
        with get_db() as db:
            wd = db.execute("SELECT * FROM withdrawals WHERE id=?", (wd_id,)).fetchone()
            if not wd:
                await update.message.reply_text("Withdrawal not found.")
                return
            if wd["status"] != "pending":
                await update.message.reply_text("Withdrawal already processed.")
                return
            if action == "approve":
                db.execute("UPDATE withdrawals SET status='done', updated_at=datetime('now') WHERE id=?", (wd_id,))
                _admin_log(db, get_internal_user_id(ADMIN_TELEGRAM_ID), "approve_withdrawal", f"WD#{wd_id}", None)
                await send_telegram(wd["user_id"], f"✅ Your withdrawal of {wd['pts_amount']} points has been approved and is being processed.")
            else:
                db.execute("UPDATE withdrawals SET status='rejected', reason=?, updated_at=datetime('now') WHERE id=?", (reason or "Rejected by admin", wd_id))
                _credit(db, wd["user_id"], wd["pts_amount"], f"Refund WD#{wd_id}")
                _admin_log(db, get_internal_user_id(ADMIN_TELEGRAM_ID), "reject_withdrawal", f"WD#{wd_id}", reason)
                await send_telegram(wd["user_id"], f"❌ Your withdrawal of {wd['pts_amount']} points was rejected. Reason: {reason or 'Rejected by admin'}. Points refunded.")
        await update.message.reply_text(f"Withdrawal {wd_id} {action}d.")

# Handle document import for admin
async def handle_import_doc(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    document = update.message.document
    if not document.file_name.endswith('.json'):
        await update.message.reply_text("Please send a JSON file.")
        return
    file = await document.get_file()
    content = await file.download_as_bytearray()
    import json
    try:
        data = json.loads(content)
    except:
        await update.message.reply_text("Invalid JSON.")
        return
    with get_db() as db:
        for table, rows in data.items():
            if table not in ["users", "transactions", "withdrawals", "settings", "claim_codes", "daily_msgs", "check_ins"]:
                continue
            for row in rows:
                placeholders = ",".join(["?"]*len(row))
                cols = ",".join(row.keys())
                db.execute(f"INSERT OR IGNORE INTO {table} ({cols}) VALUES ({placeholders})", tuple(row.values()))
    await update.message.reply_text("Import completed successfully.")
    
async def test_send(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Test if send_telegram works"""
    telegram_id = update.effective_user.id
    await send_telegram(telegram_id, "✅ Test message from bot. If you see this, send_telegram works!", parse_mode="Markdown")
    await update.message.reply_text("Test message sent. Check if you received it.")
    
async def wacash_creds_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show current WorkGo1 account (admin only)"""
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    acct = get_setting("wacash_account", "")
    if acct:
        await update.message.reply_text(f"Current WorkGo1 account: `{acct}`\nUse `/set_wacash <phone> <password>` to update.")
    else:
        await update.message.reply_text("No WorkGo1 credentials set. Use `/set_wacash <phone> <password>`.")

async def set_wacash_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Set WorkGo1 credentials (admin only)"""
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    args = context.args
    if len(args) != 2:
        await update.message.reply_text("Usage: `/set_wacash <phone> <password>`")
        return
    phone, pwd = args[0], args[1]
    with get_db() as db:
        db.execute("INSERT OR REPLACE INTO settings(key, value) VALUES('wacash_account', ?)", (phone,))
        db.execute("INSERT OR REPLACE INTO settings(key, value) VALUES('wacash_password', ?)", (pwd,))
    if wacash_login():
        await update.message.reply_text("✅ Credentials saved and login successful.")
    else:
        await update.message.reply_text("⚠️ Credentials saved, but login failed. Check the details.")
        
async def debug_mode(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Debug: Check and fix mode switching"""
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    
    # Check current mode
    current_mode = get_earning_mode()
    
    # Check what's actually in database
    with get_db() as db:
        row = db.execute("SELECT value FROM settings WHERE key='earning_mode'").fetchone()
        db_value = row["value"] if row else "NOT FOUND"
    
    # Check wacash credentials
    acct = get_setting("wacash_account", "")
    pwd = get_setting("wacash_password", "")
    
    await update.message.reply_text(
        f"📊 *Mode Debug*\n\n"
        f"get_earning_mode() returns: `{current_mode}`\n"
        f"Database value: `{db_value}`\n"
        f"Wacash account: `{acct if acct else 'NOT SET'}`\n"
        f"Wacash password: `{'✅ SET' if pwd else 'NOT SET'}`\n\n"
        f"To force set Wacash mode, send:\n`/force_mode wacash`\n\n"
        f"To force set Manual mode, send:\n`/force_mode manual`",
        parse_mode="Markdown"
    )

async def force_mode(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Force set earning mode"""
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    
    args = context.args
    if len(args) != 1 or args[0] not in ["manual", "auto", "wacash"]:
        await update.message.reply_text("Usage: `/force_mode manual|auto|wacash`")
        return
    
    new_mode = args[0]
    
    # Direct database update
    with get_db() as db:
        db.execute("INSERT OR REPLACE INTO settings(key, value) VALUES('earning_mode', ?)", (new_mode,))
    
    # Also update via set_setting to be safe
    set_setting("earning_mode", new_mode)
    
    if new_mode == "wacash":
        threading.Thread(target=wacash_login, daemon=True).start()
    
    await update.message.reply_text(f"✅ Force set earning mode to **{new_mode}**.\nRestart the bot or test by adding a number.", parse_mode="Markdown")
    
async def test_wacash_api(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Test WorkGo1 API directly"""
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    
    await update.message.reply_text("🔄 Testing WorkGo1 API...")
    
    # Check credentials
    acct = get_setting("wacash_account", "")
    pwd = get_setting("wacash_password", "")
    
    if not acct or not pwd:
        await update.message.reply_text("❌ No WorkGo1 credentials set. Use `/set_wacash <phone> <password>` first.")
        return
    
    # Try login
    if wacash_login():
        await update.message.reply_text(f"✅ Logged in as {acct}")
        
        # Test getting online numbers
        online = wacash_get_online()
        await update.message.reply_text(f"📱 Online numbers: {len(online)} found")
        
        # Test getting task info
        task_info = wacash_get_task_info()
        await update.message.reply_text(f"📊 Today's sends: {task_info.get('todaySendNum', 0)}")
    else:
        await update.message.reply_text("❌ Login failed. Check credentials.")

async def get_threads_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show current wacash threads setting"""
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    threads = get_setting("wacash_threads", "20")
    await update.message.reply_text(f"Current Wacash threads per batch: **{threads}**\n\nEach number sends {threads} concurrent requests until offline.", parse_mode="Markdown")
    
async def get_rate_settings(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show current points and naira settings"""
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    
    points_per_msg = get_setting("points_per_msg", "200")
    naira_per_msg = get_setting("naira_per_msg", "30")
    
    await update.message.reply_text(
        f"📊 *Current Rate Settings*\n\n"
        f"💰 Points per message: **{points_per_msg}** points\n"
        f"💵 Naira per point: **₦{naira_per_msg}**\n\n"
        f"*Value per message:* {int(points_per_msg)} points = ₦{int(points_per_msg) * float(naira_per_msg):.2f}\n\n"
        f"*Note:* Changing these settings only affects FUTURE earnings.\n"
        f"Existing user balances remain unchanged.",
        parse_mode="Markdown"
    )
    
async def fix_user_mode(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Force set user to hourly mode (temporary fix)"""
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        await update.message.reply_text("Unauthorized.")
        return
    
    args = context.args
    if len(args) != 1:
        await update.message.reply_text("Usage: /fix_user_mode <telegram_id>")
        return
    
    target_id = int(args[0])
    
    with get_db() as db:
        db.execute("UPDATE users SET earning_mode = 'hourly' WHERE telegram_id = ?", (target_id,))
        user = db.execute("SELECT id, username FROM users WHERE telegram_id = ?", (target_id,)).fetchone()
    
    if user:
        await update.message.reply_text(f"✅ User {user['username']} (ID: {target_id}) set to HOURLY mode.")
    else:
        await update.message.reply_text(f"❌ User with Telegram ID {target_id} not found.")
    
# ── LIVE ANIMATION ENGINE ────────────────────────────────────────────────────
# Cycling dot bars that animate in real-time while the bot is working.
# Each spinner runs its own asyncio Task so the bot stays fully responsive.

_ANIM_FRAMES = {
    "default": ["⠋","⠙","⠹","⠸","⠼","⠴","⠦","⠧","⠇","⠏"],
    "dots":    ["   ","·  ","·· ","···","·· ","·  "],
    "bar":     ["▱▱▱▱▱","▰▱▱▱▱","▰▰▱▱▱","▰▰▰▱▱","▰▰▰▰▱","▰▰▰▰▰"],
    "pulse":   ["○","◎","●","◎"],
    "link":    ["🔗","🔐","🔑","✅"],
    "send":    ["📤","📨","📩","📬","📭","📬"],
    "search":  ["🔍","🔎","🧐","🔬"],
    "clock":   ["🕐","🕑","🕒","🕓","🕔","🕕","🕖","🕗","🕘","🕙","🕚","🕛"],
}

async def _animate_loop(bot, chat_id: int, msg_id: int,
                        label: str, style: str = "default"):
    """Background task that edits the message every 1.2s to animate."""
    frames = _ANIM_FRAMES.get(style, _ANIM_FRAMES["default"])
    i = 0
    while True:
        try:
            await bot.edit_message_text(
                chat_id=chat_id,
                message_id=msg_id,
                text=f"{frames[i % len(frames)]}  {label}",
                parse_mode="Markdown"
            )
        except Exception:
            pass
        i += 1
        await asyncio.sleep(1.2)

async def show_spinner(update: Update, context: ContextTypes.DEFAULT_TYPE,
                       text: str = "Processing", style: str = "default") -> None:
    """
    Send an animated loading message and start the live animation loop.
    The message edits itself every 1.2 seconds until stop_spinner() is called.
    """
    frames = _ANIM_FRAMES.get(style, _ANIM_FRAMES["default"])
    msg = await update.message.reply_text(f"{frames[0]}  {text}")
    chat_id = update.effective_chat.id

    # Cancel any existing spinner task for this user
    old_task = context.user_data.pop("_spinner_task", None)
    if old_task and not old_task.done():
        old_task.cancel()

    # Start live animation task
    task = asyncio.create_task(
        _animate_loop(context.bot, chat_id, msg.message_id, text, style)
    )
    context.user_data["_spinner_task"]    = task
    context.user_data["spinner_msg_id"]   = msg.message_id
    context.user_data["spinner_chat_id"]  = chat_id
    context.user_data["spinner_text"]     = text
    return msg

async def update_spinner(context: ContextTypes.DEFAULT_TYPE,
                          new_text: str = None, style: str = None) -> None:
    """Change the label shown in the live spinner without stopping it."""
    if new_text:
        context.user_data["spinner_text"] = new_text
    task = context.user_data.get("_spinner_task")
    if task and not task.done():
        task.cancel()
    chat_id  = context.user_data.get("spinner_chat_id")
    msg_id   = context.user_data.get("spinner_msg_id")
    label    = new_text or context.user_data.get("spinner_text", "Processing")
    st       = style or "default"
    if chat_id and msg_id:
        new_task = asyncio.create_task(
            _animate_loop(context.bot, chat_id, msg_id, label, st)
        )
        context.user_data["_spinner_task"] = new_task

async def stop_spinner(context: ContextTypes.DEFAULT_TYPE,
                        final_text: str, success: bool = True,
                        parse_mode: str = "Markdown") -> None:
    """Stop the animation and replace with the final result message."""
    task = context.user_data.pop("_spinner_task", None)
    if task and not task.done():
        task.cancel()
    icon = "✅" if success else "❌"
    try:
        await context.bot.edit_message_text(
            chat_id=context.user_data.get("spinner_chat_id"),
            message_id=context.user_data.get("spinner_msg_id"),
            text=f"{icon}  {final_text}",
            parse_mode=parse_mode
        )
    except Exception:
        pass
    context.user_data.pop("spinner_msg_id", None)
    context.user_data.pop("spinner_chat_id", None)

async def update_spinner_message(msg, new_text: str):
    """Lightweight edit helper for messages outside the spinner system."""
    try:
        await msg.edit_text(f"⏳  {new_text}", parse_mode="Markdown")
    except Exception:
        pass

# ----------------------------------------------------------------------
# Main bot setup
# ----------------------------------------------------------------------
async def post_init(app):
    """
    Called once the event loop is running inside run_polling().
    Safe place to start Telethon worker and set _bot_loop.
    """
    global _bot_loop, _application
    _application = app
    _bot_loop = asyncio.get_event_loop()
    
    # Start Task4U login for hourly mode in background
    def start_task4u_login():
        task4u_login()
        log.info("[Task4U] Initial login complete")
    
    # Run Task4U login in thread pool to avoid blocking
    loop = asyncio.get_event_loop()
    await loop.run_in_executor(None, start_task4u_login)
    
    log.info("[Bot] post_init: starting Telethon task worker...")
    await _start_task_worker()
    
    # Start hourly monitoring tasks
    asyncio.create_task(realtime_hourly_monitor())
    asyncio.create_task(hourly_payout_monitor())
    
    log.info("[Bot] post_init: complete.")

def _session_keepalive():
    """Keep platform session alive (same as original)."""
    while True:
        time.sleep(600)
        try:
            s = dict(platform_session)
            if not s.get("http"):
                platform_login()
                continue
            sign = _s0("/api/user/get_appinfo", str(s["userid"]), s["username"])
            r = s["http"].get(f"{BASE_URL}/api/user/get_appinfo",
                params={"page": 1, "pagesize": 1, "username": s["username"],
                        "userid": s["userid"], "sign": sign},
                headers=_hdrs(), timeout=10)
            if r.json().get("code") != 0:
                platform_login()
        except Exception:
            platform_login()

def main():
    global _application, _bot_loop
    token = "8461339264:AAH6UfCD3R3u2-vjFyPAKDXvhrkdYCYg06s"
    if not token:
        log.error("TELEGRAM_BOT_TOKEN environment variable not set.")
        return
    application = Application.builder().token(token).build()
    _application = application

    # Conversation handlers
    add_number_conv = ConversationHandler(
        entry_points=[MessageHandler(filters.Regex("^➕ Add Number$"), add_number_start)],
        states={TYPING_NUMBER: [MessageHandler(filters.TEXT & ~filters.COMMAND, add_number_receive)]},
        fallbacks=[CommandHandler("cancel", cancel)]
    )
    withdraw_conv = ConversationHandler(
        entry_points=[MessageHandler(filters.Regex("^💸 Withdraw$"), withdraw_start)],
        states={
            SELECTING_WITHDRAW_METHOD: [CallbackQueryHandler(withdraw_method_callback, pattern="^with_")],
            TYPING_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, withdraw_amount_receive)],
            TYPING_PASSWORD: [MessageHandler(filters.TEXT & ~filters.COMMAND, withdraw_password_receive)]
        },
        fallbacks=[CommandHandler("cancel", cancel)]
    )

    # Register handlers
    application.add_handler(CommandHandler("start", start))
    application.add_handler(CallbackQueryHandler(mode_choice_callback, pattern="^mode_"))
    application.add_handler(CallbackQueryHandler(number_action_callback, pattern="^(delnum_|reauthnum_|linkagain_)"))
    application.add_handler(CallbackQueryHandler(admin_panel_callback, pattern="^admin_"))
    application.add_handler(CallbackQueryHandler(admin_panel_callback, pattern="^mode_"))
    application.add_handler(CallbackQueryHandler(admin_panel_callback, pattern="^earn_"))
    application.add_handler(CallbackQueryHandler(settings_callback, pattern="^sett_"))
    application.add_handler(MessageHandler(filters.Regex("^💰 Dashboard$"), dashboard))
    application.add_handler(add_number_conv)
    application.add_handler(MessageHandler(filters.Regex("^📞 My Numbers$"), my_numbers))
    application.add_handler(MessageHandler(filters.Regex("^✉️ Send All$"), send_all))
    application.add_handler(MessageHandler(filters.Regex("^🏆 Leaderboard$"), leaderboard))
    application.add_handler(MessageHandler(filters.Regex("^🎁 Check-in$"), check_in))
    application.add_handler(withdraw_conv)
    application.add_handler(MessageHandler(filters.Regex("^🔗 Referral$"), referral))
    application.add_handler(MessageHandler(filters.Regex("^⚙️ Settings$"), settings_menu))
    application.add_handler(MessageHandler(filters.Regex("^👑 Admin Panel$"), lambda u,c: u.message.reply_text("Admin Panel:", reply_markup=admin_panel_markup)))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & ~filters.Regex("^[➕💰📞✉️🏆🎁💸🔗⚙️👑]"), handle_settings_input))
    # Admin commands
    application.add_handler(CommandHandler("credit_user", admin_command_handler))
    application.add_handler(CommandHandler("ban_user", admin_command_handler))
    application.add_handler(CommandHandler("gen_code", admin_command_handler))
    application.add_handler(CommandHandler("broadcast", admin_command_handler))
    application.add_handler(CommandHandler("testsend", test_send))
    application.add_handler(CommandHandler("admin_withdraw", admin_command_handler))
    application.add_handler(MessageHandler(filters.Document.ALL, handle_import_doc))
    application.add_handler(CommandHandler("wacash_creds", wacash_creds_command))
    application.add_handler(CommandHandler("set_wacash", set_wacash_command))
    application.add_handler(CommandHandler("debug_mode", debug_mode))
    application.add_handler(CommandHandler("force_mode", force_mode))
    application.add_handler(CommandHandler("testwacash", test_wacash_api))
    application.add_handler(CommandHandler("threads", get_threads_command))
    application.add_handler(CommandHandler("rates", get_rate_settings))
    application.add_handler(CallbackQueryHandler(set_mode_callback, pattern="^set_mode_"))
    application.add_handler(MessageHandler(filters.Regex("^⚡ Hourly Status$"), hourly_status))
    application.add_handler(CommandHandler("fix_user_mode", fix_user_mode))

    # Initialize database and start background tasks
    init_db()

    # Start platform session in background thread (non-blocking)
    threading.Thread(target=platform_login, daemon=True).start()
    if get_earning_mode() == "wacash":
        threading.Thread(target=wacash_login, daemon=True).start()

    # Keep platform session alive
    threading.Thread(target=_session_keepalive, daemon=True).start()

    # ✅ ATTACH post_init handler (MUST be done before run_polling)
    application.post_init = post_init

    # Start the bot
    application.run_polling(allowed_updates=Update.ALL_TYPES)

if __name__ == "__main__":
    main()
