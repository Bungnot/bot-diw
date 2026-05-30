# app.py â€” LINE Bungfai Bot (Flask + line-bot-sdk)
# (c) SITTIPONG â€” hardened, anti-abuse, anti-kick, 1-bill-per-round, @mention admin/mod, uid lookup

from dotenv import load_dotenv
load_dotenv()


from waitress import serve

import os, re, time, base64, json, tempfile
from datetime import datetime
from hmac import new as hmac_new, compare_digest
from hashlib import sha256
from html import escape as html_escape
from math import ceil, floor
from collections import deque
from functools import lru_cache
import threading


from contextlib import contextmanager

# ==== REGEX (precompiled) ====
R_PARSE_BET = re.compile(r"^([à¸¥à¸ªà¸¢à¸•])\s*[\/\s]*([0-9]+)$", re.IGNORECASE)
R_O         = re.compile(r"^\s*o\b", re.IGNORECASE)
R_ANN = re.compile(
    r"^\s*([^\s].+?)\s*à¸¥\s*(\d+)\s*[-/]\s*(\d+)\s*à¸¢\s*(\d+)\s*[-/]\s*(\d+)\s*$",
    re.IGNORECASE
)
R_O_ANN = re.compile(
    r"^\s*o\s+(.+?)\s*à¸¥\s*(\d+)\s*[-/]\s*(\d+)\s*à¸¢\s*(\d+)\s*[-/]\s*(\d+)\s*$",
    re.IGNORECASE
)
R_CLEAR     = re.compile(r"^(clear|reset)\b", re.IGNORECASE)
R_CM        = re.compile(r"^cm$", re.IGNORECASE)
R_CALL      = re.compile(r"^call$", re.IGNORECASE)
R_UID       = re.compile(r"^uid\b", re.IGNORECASE)
R_SET_RESULT= re.compile(r"^[sS]\s*(.+)$")
R_MUTING    = re.compile(r"^(ban|unban|mute|unmute)\b(?:\s+(.*))?$", re.IGNORECASE)
R_CANCEL_BY_CID = re.compile(r"^x\s+(\d+)$", re.IGNORECASE)
R_ADMIN_ADD = re.compile(
    r"^\s*(?:admin(?:\s+add)?|à¹€à¸žà¸´à¹ˆà¸¡à¹à¸­à¸”à¸¡à¸´à¸™)(?:\s+|(?=@)|$)",
    re.IGNORECASE
)
R_ADMIN_DEL   = re.compile(r"^\s*(?:admin\s+del|à¸¥à¸šà¹à¸­à¸”à¸¡à¸´à¸™)\b", re.IGNORECASE)
R_ADMIN_LIST  = re.compile(r"^\s*(?:admin\s+list|à¹€à¸Šà¹‡à¸„à¹à¸­à¸”à¸¡à¸´à¸™|à¸£à¸²à¸¢à¸Šà¸·à¹ˆà¸­à¹à¸­à¸”à¸¡à¸´à¸™)\s*$", re.IGNORECASE)
R_CLOSE_TH    = re.compile(r"^(à¸›à¸´à¸”à¸£à¸­à¸š|à¸«à¸¢à¸¸à¸”à¹à¸—à¸‡|à¸›à¸´à¸”)$")
R_YCONFIRM    = re.compile(r"^(?:T/|/Y|Y)\s*$", re.IGNORECASE)
R_CLEAR_PROFIT = re.compile(r"^à¸¥à¹‰à¸²à¸‡à¸à¸³à¹„à¸£$", re.IGNORECASE)
R_GETID = re.compile(r"^getid\b", re.IGNORECASE)
R_DEL_USER = re.compile(r"^del\s+(\d+)$", re.IGNORECASE)



# ====== GLOBAL LOCKS ======
_users_lock = threading.RLock()
_rooms_lock = threading.RLock()

# ====== WEBHOOK IDEMPOTENCY / à¸à¸±à¸™ LINE retry à¸›à¸£à¸°à¸¡à¸§à¸¥à¸œà¸¥à¸‹à¹‰à¸³ ======
# LINE à¸­à¸²à¸ˆà¸ªà¹ˆà¸‡ event à¹€à¸”à¸´à¸¡à¸‹à¹‰à¸³à¹„à¸”à¹‰ à¸–à¹‰à¸² webhook à¸•à¸­à¸šà¸Šà¹‰à¸²/timeout
_processed_msg_lock = threading.RLock()
_processed_msg_ids = {}  # message_id -> timestamp
PROCESSED_MSG_TTL_SEC = int(os.getenv("PROCESSED_MSG_TTL_SEC", "900"))

def already_processed_message(message_id: str) -> bool:
    """à¸„à¸·à¸™ True à¸–à¹‰à¸² message id à¸™à¸µà¹‰à¹€à¸„à¸¢à¸–à¸¹à¸à¸›à¸£à¸°à¸¡à¸§à¸¥à¸œà¸¥à¹à¸¥à¹‰à¸§"""
    if not message_id:
        return False
    now = time.time()
    with _processed_msg_lock:
        # à¹€à¸à¹‡à¸š cache à¹ƒà¸«à¹‰à¹€à¸¥à¹‡à¸ à¹„à¸¡à¹ˆà¹ƒà¸«à¹‰ RAM à¸šà¸§à¸¡
        for mid, ts in list(_processed_msg_ids.items()):
            if now - ts > PROCESSED_MSG_TTL_SEC:
                _processed_msg_ids.pop(mid, None)

        if message_id in _processed_msg_ids:
            return True

        _processed_msg_ids[message_id] = now
        return False


def has_active_bet(uid):
    for stx in rooms.values():
        if uid in stx.get("bet_index", {}):
            return True
    return False


@contextmanager
def with_users_lock():
    _users_lock.acquire()
    try:
        yield
    finally:
        _users_lock.release()

@contextmanager
def with_rooms_lock():
    _rooms_lock.acquire()
    try:
        yield
    finally:
        _rooms_lock.release()


from flask import Flask, request, make_response
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError
from linebot.models import (
    MessageEvent, TextMessage, TextSendMessage,
    FlexSendMessage, UnsendEvent,
    MemberJoinedEvent, MemberLeftEvent,
    ImageMessage,   # <<< à¹€à¸žà¸´à¹ˆà¸¡à¸šà¸£à¸£à¸—à¸±à¸”à¸™à¸µà¹‰
)


# ====== CONFIG (à¸›à¸£à¸±à¸šà¹„à¸”à¹‰) ======
DEPOSIT_URL = os.getenv("DEPOSIT_URL", "https://page.line.me/957gvogc")
PROFIT_RATE = float(os.getenv("PROFIT_RATE", "0.95"))   # à¸Šà¸™à¸°à¸«à¸±à¸ 5% = à¸ˆà¹ˆà¸²à¸¢à¸ªà¸¸à¸—à¸˜à¸´ 1:0.95
MIDDLE_FEE  = float(os.getenv("MIDDLE_FEE",  "0.03"))   # à¸«à¸±à¸à¹€à¸¡à¸·à¹ˆà¸­à¸„à¸·à¸™à¹€à¸‡à¸´à¸™ (à¸à¸¥à¸²à¸‡/à¹€à¸ªà¸¡à¸­à¹à¸šà¸šà¸«à¸±à¸)
MIN_BET = int(os.getenv("MIN_BET", "30"))
MAX_BET = int(os.getenv("MAX_BET", "10000"))
USER_SIDE_CAP = {"HI": 10000, "LO": 10000}
SIDE_CAP      = {"HI": 50000, "LO": 30000}
ROUND_CAP     = 80000

# ====== SIMPLE PER-USER COOLDOWN (anti-spam reply gap) ======
REPLY_COOLDOWN_SEC = int(os.getenv("REPLY_COOLDOWN_SEC", "6"))
_LAST_REPLIED_AT = {}        # scope_key -> epoch seconds
_COOLDOWN_LOCK = threading.Lock()  # <<< à¹€à¸žà¸´à¹ˆà¸¡à¸•à¸±à¸§à¸¥à¹‡à¸­à¸

def _should_reply_now(scope_key: str) -> bool:
    """
    à¸›à¹‰à¸­à¸‡à¸à¸±à¸™à¸•à¸­à¸šà¸–à¸µà¹ˆà¹€à¸à¸´à¸™à¹„à¸›à¹à¸šà¸šà¸­à¸°à¸•à¸­à¸¡à¸´à¸: à¹€à¸Šà¹‡à¸„ + à¸­à¸±à¸›à¹€à¸”à¸• à¸ à¸²à¸¢à¹ƒà¸•à¹‰à¸¥à¹‡à¸­à¸à¹€à¸”à¸µà¸¢à¸§à¸à¸±à¸™
    scope_key = à¸„à¸µà¸¢à¹Œà¸ªà¸³à¸«à¸£à¸±à¸šà¸„à¸¹à¸¥à¸”à¸²à¸§à¸™à¹Œ (à¹€à¸Šà¹ˆà¸™ uid:room)
    """
    if REPLY_COOLDOWN_SEC <= 0:
        return True
    now = _now()
    with _COOLDOWN_LOCK:  # <<< à¸¥à¹‡à¸­à¸à¸à¸±à¸™à¸Šà¸™à¸à¸±à¸™à¸‚à¹‰à¸²à¸¡à¹€à¸˜à¸£à¸”
        last = _LAST_REPLIED_AT.get(scope_key, 0)
        if (now - last) < REPLY_COOLDOWN_SEC:
            return False
        _LAST_REPLIED_AT[scope_key] = now
        return True



# ====== PERSISTENCE (users + nextCustomerId) ======
DATA_DIR = os.getenv("DATA_DIR", "./data")
os.makedirs(DATA_DIR, exist_ok=True)

# Copy default data files if not exists
import shutil
for _fname in ["users.json", "admins.json"]:
    _src = os.path.join("data", _fname)
    _dst = os.path.join(DATA_DIR, _fname)
    if not os.path.exists(_dst) and os.path.exists(_src):
        shutil.copy2(_src, _dst)
        
# ====== LAST SETTLE (free backoffice) ======
LAST_SETTLE_JSON = os.path.join(DATA_DIR, "last_settle_global.json")

def save_last_settle(payload: dict):
    """à¹€à¸à¹‡à¸šà¸ªà¸£à¸¸à¸›à¸¥à¹ˆà¸²à¸ªà¸¸à¸”à¹„à¸§à¹‰à¹ƒà¸«à¹‰à¸«à¸¥à¸±à¸‡à¸šà¹‰à¸²à¸™à¹€à¸£à¸µà¸¢à¸à¸”à¸¹à¹„à¸”à¹‰ à¹‚à¸”à¸¢à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡ push (à¸›à¸£à¸°à¸«à¸¢à¸±à¸”à¹‚à¸„à¸§à¸•à¹‰à¸²)"""
    try:
        _atomic_write_json(LAST_SETTLE_JSON, payload)
    except Exception:
        app.logger.exception("save_last_settle failed")

def load_last_settle():
    try:
        if not os.path.exists(LAST_SETTLE_JSON):
            return None
        with open(LAST_SETTLE_JSON, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        app.logger.exception("load_last_settle failed")
        return None

def settle_payload_to_text(p: dict) -> str:
    """à¹à¸›à¸¥à¸‡ payload à¹€à¸›à¹‡à¸™à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸ªà¸±à¹‰à¸™ à¹† (Text)
    à¸«à¸¡à¸²à¸¢à¹€à¸«à¸•à¸¸: à¹à¸ªà¸”à¸‡ 'à¹„à¸”à¹‰à¹€à¸ªà¸µà¸¢' = payout - stake (à¸¡à¸¸à¸¡à¸¡à¸­à¸‡à¸¥à¸¹à¸à¸„à¹‰à¸²)
             à¹à¸¥à¸° 'à¸à¸³à¹„à¸£à¸£à¸­à¸šà¸™à¸µà¹‰' = à¸¡à¸¸à¸¡à¸¡à¸­à¸‡à¹€à¸ˆà¹‰à¸²à¸¡à¸·à¸­ (profit = stake - payout)
    """
    try:
        def _fmt(n):
            try:
                # à¸£à¸­à¸‡à¸£à¸±à¸š int/float/str
                if n is None:
                    n = 0
                n = float(n)
                if n.is_integer():
                    return f"{int(n):,}"
                return f"{n:,.2f}"
            except Exception:
                return str(n)

        def _signed(n):
            try:
                n = float(n or 0)
            except Exception:
                n = 0
            return f"+{_fmt(n)}" if n >= 0 else f"-{_fmt(abs(n))}"

        round_no = p.get("round")
        camp = p.get("camp_name") or "-"
        code = p.get("code") or "-"
        profit = p.get("profit", 0)  # à¸¡à¸¸à¸¡à¸¡à¸­à¸‡à¹€à¸ˆà¹‰à¸²à¸¡à¸·à¸­
        accum = p.get("accum") or {}
        net = accum.get("net", 0)
        ts = p.get("ts_iso") or ""

        rows = p.get("rows") or []
        lines = []
        for r in rows[:12]:  # à¸à¸±à¸™à¸¢à¸²à¸§à¹€à¸à¸´à¸™
            name = r.get("name") or r.get("uid") or "-"
            stake = r.get("stake", 0) or 0
            payout = r.get("payout", 0) or 0
            pl = payout - stake  # à¸¡à¸¸à¸¡à¸¡à¸­à¸‡à¸¥à¸¹à¸à¸„à¹‰à¸² (à¹„à¸”à¹‰à¹€à¸ªà¸µà¸¢)
            # à¸–à¹‰à¸²à¸¡à¸µ bet à¸à¹‡à¹à¸ªà¸”à¸‡à¹à¸šà¸šà¸ªà¸±à¹‰à¸™ à¹†
            bet = (r.get("bet") or "").strip()
            bet_txt = f" [{bet}]" if bet else ""
            lines.append(f"- {name}{bet_txt} {_signed(pl)}")
        if len(rows) > 12:
            lines.append(f"...à¹à¸¥à¸°à¸­à¸µà¸ {len(rows)-12} à¸£à¸²à¸¢")

        return (
            f"ðŸ“Œ à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸£à¸­à¸š {round_no} | à¸„à¹ˆà¸²à¸¢: {camp} | à¸œà¸¥: {code}\n"
            f"à¸¥à¸¹à¸à¸„à¹‰à¸²: {len(rows)} à¸„à¸™\n"
            f"ðŸ’° à¸à¸³à¹„à¸£à¸£à¸­à¸šà¸™à¸µà¹‰ (à¹€à¸ˆà¹‰à¸²à¸¡à¸·à¸­): {_signed(profit)}\n"
            f"ðŸ§® à¸à¸³à¹„à¸£à¸ªà¸¸à¸—à¸˜à¸´à¸ªà¸°à¸ªà¸¡: {_signed(net)}\n"
            f"ðŸ•’ à¹€à¸§à¸¥à¸²: {ts}\n\n"
            + ("\n".join(lines) if lines else "")
        ).strip()
    except Exception:
        app.logger.exception("settle_payload_to_text failed")
        return "ðŸ“Œ à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸¥à¹ˆà¸²à¸ªà¸¸à¸” (à¹à¸›à¸¥à¸‡à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¹„à¸¡à¹ˆà¸ªà¸³à¹€à¸£à¹‡à¸ˆ)"


USERS_JSON = os.path.join(DATA_DIR, "users.json")
_user_store_lock = threading.Lock()


# --- JSON encoder/decoder with orjson fallback ---
try:
    import orjson as _orjson
    def _dumps_bytes(obj) -> bytes:
        return _orjson.dumps(obj)               # à¹„à¸”à¹‰ bytes à¹€à¸¥à¸¢
    def _loads_bytes(buf: bytes):
        return _orjson.loads(buf)
except Exception:
    import json as _json
    def _dumps_bytes(obj) -> bytes:
        # à¹ƒà¸«à¹‰à¹„à¸”à¹‰ bytes à¹€à¸«à¸¡à¸·à¸­à¸™ orjson
        return _json.dumps(
            obj,
            ensure_ascii=False,
            separators=(",", ":")
        ).encode("utf-8")
    def _loads_bytes(buf: bytes):
        return _json.loads(buf.decode("utf-8"))

def _atomic_write_json(path: str, data: dict):
    dirname = os.path.dirname(path) or "."
    fd, tmp = tempfile.mkstemp(prefix=".tmp_", dir=dirname)
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(_dumps_bytes(data))
        os.replace(tmp, path)  # atomic replace
    except Exception:
        try:
            os.remove(tmp)
        except Exception:
            pass
        raise


# ====== ADMIN ACTION GUARD ======
# à¸à¸±à¸™à¹à¸­à¸”à¸¡à¸´à¸™à¸à¸”à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸‹à¹‰à¸­à¸™ à¸—à¸±à¹‰à¸‡à¹ƒà¸™à¸£à¸°à¸”à¸±à¸š thread à¹à¸¥à¸° process à¹€à¸”à¸µà¸¢à¸§à¸à¸±à¸™
# à¹ƒà¸Šà¹‰à¹„à¸Ÿà¸¥à¹Œ state à¹€à¸žà¸·à¹ˆà¸­à¸à¸±à¸™à¹€à¸„à¸ªà¸—à¸µà¹ˆ server à¸¡à¸µà¸«à¸¥à¸²à¸¢ worker à¹à¸¥à¹‰à¸§ memory rooms à¹„à¸¡à¹ˆ sync à¸à¸±à¸™
_ADMIN_ACTION_STATE_JSON = os.path.join(DATA_DIR, "admin_action_state.json")
_ADMIN_ACTION_LOCK_FILE = os.path.join(DATA_DIR, ".admin_action.lock")
_ADMIN_ACTION_TTL_SEC = int(os.getenv("ADMIN_ACTION_TTL_SEC", "86400"))
_admin_action_thread_lock = threading.RLock()

@contextmanager
def _admin_action_file_lock():
    os.makedirs(DATA_DIR, exist_ok=True)
    with _admin_action_thread_lock:
        with open(_ADMIN_ACTION_LOCK_FILE, "a+b") as f:
            locked = False
            try:
                try:
                    import fcntl
                    fcntl.flock(f.fileno(), fcntl.LOCK_EX)
                    locked = True
                except Exception:
                    # Windows à¸«à¸£à¸·à¸­ environment à¸—à¸µà¹ˆà¹„à¸¡à¹ˆà¸¡à¸µ fcntl à¸ˆà¸°à¸¢à¸±à¸‡à¸à¸±à¸™à¸‹à¹‰à¸­à¸™à¹ƒà¸™ process à¸”à¹‰à¸§à¸¢ thread lock
                    locked = False
                yield
            finally:
                if locked:
                    try:
                        import fcntl
                        fcntl.flock(f.fileno(), fcntl.LOCK_UN)
                    except Exception:
                        pass

def _load_admin_action_state() -> dict:
    try:
        if not os.path.exists(_ADMIN_ACTION_STATE_JSON):
            return {}
        with open(_ADMIN_ACTION_STATE_JSON, "rb") as f:
            data = _loads_bytes(f.read())
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def _save_admin_action_state(data: dict):
    _atomic_write_json(_ADMIN_ACTION_STATE_JSON, data)

def _admin_action_key(action: str, room_id: str, pair_no) -> str:
    raw = f"{action}|{room_id}|{pair_no}".encode("utf-8")
    return sha256(raw).hexdigest()

def claim_round_action(action: str, room_id: str, pair_no, uid: str = None):
    """à¸ˆà¸­à¸‡ action à¸•à¹ˆà¸­à¸«à¹‰à¸­à¸‡/à¸£à¸­à¸šà¹à¸šà¸š atomic
    return (True, None) à¸–à¹‰à¸²à¸ˆà¸­à¸‡à¸ªà¸³à¹€à¸£à¹‡à¸ˆ
    return (False, old_info) à¸–à¹‰à¸²à¸¡à¸µà¸„à¸™à¸—à¸³ action à¸™à¸µà¹‰à¹„à¸›à¹à¸¥à¹‰à¸§
    """
    if not room_id or not pair_no:
        return True, None

    now = time.time()
    with _admin_action_file_lock():
        data = _load_admin_action_state()

        # à¸¥à¹‰à¸²à¸‡à¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¹€à¸à¹ˆà¸² à¸à¸±à¸™à¹„à¸Ÿà¸¥à¹Œà¹‚à¸•à¹à¸¥à¸°à¸à¸±à¸™à¸£à¸­à¸šà¹€à¸à¹ˆà¸²à¸„à¹‰à¸²à¸‡à¸‚à¹‰à¸²à¸¡à¸§à¸±à¸™
        for k, v in list(data.items()):
            try:
                if now - float(v.get("ts", 0)) > _ADMIN_ACTION_TTL_SEC:
                    data.pop(k, None)
            except Exception:
                data.pop(k, None)

        k = _admin_action_key(action, str(room_id), pair_no)
        old = data.get(k)
        if old:
            _save_admin_action_state(data)
            return False, old

        data[k] = {
            "action": action,
            "room_id": str(room_id),
            "pair_no": pair_no,
            "uid": uid,
            "ts": now,
            "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        }
        _save_admin_action_state(data)
        return True, None

def release_round_action(action: str, room_id: str, pair_no):
    """à¸›à¸¥à¸”à¸¥à¹‡à¸­à¸ action à¹€à¸‰à¸žà¸²à¸°à¸à¸£à¸“à¸µà¸•à¸±à¹‰à¸‡à¹ƒà¸ˆà¸à¸¥à¸±à¸šà¸¡à¸²à¹€à¸›à¸´à¸”à¸£à¸­à¸šà¹€à¸”à¸´à¸¡ à¹€à¸Šà¹ˆà¸™ R/RESUME"""
    if not room_id or not pair_no:
        return
    with _admin_action_file_lock():
        data = _load_admin_action_state()
        data.pop(_admin_action_key(action, str(room_id), pair_no), None)
        _save_admin_action_state(data)

def has_round_action(action: str, room_id: str, pair_no) -> bool:
    """à¹€à¸Šà¹‡à¸„à¸§à¹ˆà¸² action à¸‚à¸­à¸‡à¸«à¹‰à¸­à¸‡/à¸£à¸­à¸šà¸™à¸µà¹‰à¹€à¸„à¸¢à¸–à¸¹à¸à¸ˆà¸­à¸‡à¹„à¸§à¹‰à¹à¸¥à¹‰à¸§à¸«à¸£à¸·à¸­à¸¢à¸±à¸‡"""
    if not room_id or not pair_no:
        return False
    now = time.time()
    with _admin_action_file_lock():
        data = _load_admin_action_state()

        changed = False
        for k, v in list(data.items()):
            try:
                if now - float(v.get("ts", 0)) > _ADMIN_ACTION_TTL_SEC:
                    data.pop(k, None)
                    changed = True
            except Exception:
                data.pop(k, None)
                changed = True

        if changed:
            _save_admin_action_state(data)

        return _admin_action_key(action, str(room_id), pair_no) in data

def get_active_round_action(action: str, room_id: str):
    """à¸„à¸·à¸™ action à¸—à¸µà¹ˆà¸¢à¸±à¸‡à¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆà¸‚à¸­à¸‡à¸«à¹‰à¸­à¸‡à¸™à¸µà¹‰ 1 à¸£à¸²à¸¢à¸à¸²à¸£ à¹€à¸Šà¹ˆà¸™ rollback à¸„à¹‰à¸²à¸‡à¸£à¸­à¸šà¹ƒà¸”à¸­à¸¢à¸¹à¹ˆ"""
    if not room_id:
        return None
    now = time.time()
    room_id = str(room_id)
    with _admin_action_file_lock():
        data = _load_admin_action_state()

        changed = False
        for k, v in list(data.items()):
            try:
                if now - float(v.get("ts", 0)) > _ADMIN_ACTION_TTL_SEC:
                    data.pop(k, None)
                    changed = True
            except Exception:
                data.pop(k, None)
                changed = True

        if changed:
            _save_admin_action_state(data)

        candidates = [
            v for v in data.values()
            if v.get("action") == action and str(v.get("room_id")) == room_id
        ]
        if not candidates:
            return None
        # à¹€à¸­à¸²à¸£à¸²à¸¢à¸à¸²à¸£à¸¥à¹ˆà¸²à¸ªà¸¸à¸”/à¹ƒà¸«à¸à¹ˆà¸ªà¸¸à¸”à¸•à¸²à¸¡à¹€à¸§à¸¥à¸² à¹€à¸žà¸·à¹ˆà¸­à¸à¸±à¸™à¸à¸£à¸“à¸µà¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¹€à¸à¹ˆà¸²à¸«à¸¥à¸‡à¹€à¸«à¸¥à¸·à¸­
        candidates.sort(key=lambda x: float(x.get("ts", 0) or 0), reverse=True)
        return candidates[0]


def _pending_rollback_snapshot_path(room_id: str) -> str:
    raw = str(room_id or "").encode("utf-8")
    h = sha256(raw).hexdigest()
    return os.path.join(DATA_DIR, f"pending_rollback_{h}.json")


def save_pending_rollback_snapshot(room_id: str, round_no: int, uid: str, st: dict):
    """à¹€à¸à¹‡à¸šà¸ªà¸–à¸²à¸™à¸°à¸à¹ˆà¸­à¸™à¸¢à¹‰à¸­à¸™ à¹€à¸žà¸·à¹ˆà¸­à¹ƒà¸«à¹‰à¸„à¸³à¸ªà¸±à¹ˆà¸‡ 'à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™ <à¸£à¸­à¸š>' à¸„à¸·à¸™à¸à¸¥à¸±à¸šà¹„à¸”à¹‰à¸­à¸¢à¹ˆà¸²à¸‡à¸›à¸¥à¸­à¸”à¸ à¸±à¸¢"""
    if not room_id or not round_no:
        return
    try:
        with with_users_lock():
            users_snapshot = _loads_bytes(_dumps_bytes(users))
        room_snapshot = _loads_bytes(_dumps_bytes(st))
        payload = {
            "round_no": int(round_no),
            "room_id": str(room_id),
            "uid": uid,
            "ts": time.time(),
            "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "users": users_snapshot,
            "room_state": room_snapshot,
            "metrics": _loads_bytes(_dumps_bytes(METRICS)),
            "last_settle": load_last_settle(),
        }
        _atomic_write_json(_pending_rollback_snapshot_path(room_id), payload)
    except Exception:
        app.logger.exception("save_pending_rollback_snapshot failed")
        raise


def load_pending_rollback_snapshot(room_id: str):
    try:
        path = _pending_rollback_snapshot_path(room_id)
        if not os.path.exists(path):
            return None
        with open(path, "rb") as f:
            data = _loads_bytes(f.read())
        return data if isinstance(data, dict) else None
    except Exception:
        app.logger.exception("load_pending_rollback_snapshot failed")
        return None


def clear_pending_rollback_snapshot(room_id: str):
    try:
        path = _pending_rollback_snapshot_path(room_id)
        if os.path.exists(path):
            os.remove(path)
    except Exception:
        app.logger.exception("clear_pending_rollback_snapshot failed")


def clear_round_action_guard(room_id: str = None):
    """à¹ƒà¸Šà¹‰à¸•à¸­à¸™ clear/reset à¹€à¸žà¸·à¹ˆà¸­à¸¥à¹‰à¸²à¸‡ guard à¸—à¸µà¹ˆà¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆ"""
    with _admin_action_file_lock():
        data = _load_admin_action_state()
        if room_id is None:
            data.clear()
        else:
            room_id = str(room_id)
            data = {k: v for k, v in data.items() if str(v.get("room_id")) != room_id}
        _save_admin_action_state(data)





def save_users_persist():
    # à¹„à¸¡à¹ˆà¹€à¸‚à¸µà¸¢à¸™à¸—à¸±à¸™à¸—à¸µ â€” à¹à¸„à¹ˆà¸ˆà¸¸à¸” event à¹ƒà¸«à¹‰ worker à¹„à¸›à¹€à¸‚à¸µà¸¢à¸™à¹€à¸›à¹‡à¸™à¸à¹‰à¸­à¸™
    _save_event.set()



def load_users_persist():
    global nextCustomerId, users
    try:
        if not os.path.exists(USERS_JSON): return
        with _user_store_lock:
            with open(USERS_JSON, "rb") as f:
                data = _loads_bytes(f.read())


        disk_users = data.get("users", {})
        disk_next = int(data.get("nextCustomerId", 0) or 0)
        with with_users_lock():
            if isinstance(disk_users, dict):
                users.clear()
                for k, v in disk_users.items():
                    users[k] = {
                        "uid": v.get("uid", k),
                        "cid": int(v.get("cid", 0) or 0),
                        "name": v.get("name", "à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™"),
                        "pictureUrl": v.get("pictureUrl"),
                        "credit": int(v.get("credit", 0) or 0),
                    }
            if disk_next > 0:
                nextCustomerId = disk_next
    except Exception:
        try:
            app.logger.exception("load_users_persist failed")
        except Exception:
            pass





# ====== LINE BOOTSTRAP ======
CHANNEL_ACCESS_TOKEN = os.getenv("LINE_CHANNEL_ACCESS_TOKEN", "REPLACE_ME")
CHANNEL_SECRET = os.getenv("LINE_CHANNEL_SECRET", "REPLACE_ME")

ADMIN_IDS = [s.strip() for s in os.getenv(
    "ADMIN_IDS", "U8e996c055ed55573b042f8119bcc5844,U3ae8e637f4da0559d906847535e35fbb,U24298c1e9f43986904ee6d3e3d10267d,Ua139e5d2bcd9606877829acc2fdcd1ec,Ua4dfc588cd253940e13c4e81188d69e8,U458603076cc4dee45ff1273e1f634ef2"
).split(",") if s.strip()]

BACKOFFICE_GROUP_IDS = {  # à¸à¸¥à¸¸à¹ˆà¸¡à¸«à¸¥à¸±à¸‡à¸šà¹‰à¸²à¸™ (à¸£à¸±à¸šà¸ªà¸£à¸¸à¸›à¸žà¸£à¹‰à¸­à¸¡à¸à¸³à¹„à¸£à¸ªà¸¸à¸—à¸˜à¸´)
    "Cab9fd7703ec00d036fa8ee94e4a59b80",
}

BASE_URL = os.getenv("BASE_URL", "https://example.ngrok-free.app")

BANK = {
    "brand": os.getenv("BANK_BRAND", "à¸à¸ªà¸´à¸à¸£à¹„à¸—à¸¢"),
    "accountNo": os.getenv("BANK_ACCOUNT", "115-336-6086"),
    "owner": os.getenv("BANK_OWNER", "à¸à¸´à¸•à¸•à¸´à¸žà¸‡à¸©à¹Œ à¸£à¸²à¸Šà¸§à¸±à¸™à¸”à¸µ"),
}
PORT = int(os.getenv("PORT", "5000"))

# ====== LINE BOT API TIMEOUT (à¹à¸à¹‰ safe_reply timeout à¹„à¸› api.line.me) ======
# à¸„à¹ˆà¸²à¹€à¸£à¸´à¹ˆà¸¡à¸•à¹‰à¸™à¸‚à¸­à¸‡ SDK à¸¡à¸±à¸à¸ªà¸±à¹‰à¸™à¹€à¸à¸´à¸™à¹„à¸› à¸—à¸³à¹ƒà¸«à¹‰ SSL/read timeout à¸‡à¹ˆà¸²à¸¢à¸•à¸­à¸™à¹€à¸™à¹‡à¸•à¸Šà¹‰à¸²
LINE_API_TIMEOUT = (
    int(os.getenv("LINE_CONNECT_TIMEOUT", "15")),  # connect timeout (à¹€à¸žà¸´à¹ˆà¸¡à¸ˆà¸²à¸ 10 â†’ 15)
    int(os.getenv("LINE_READ_TIMEOUT", "30")),     # read timeout
)
LINE_API_RETRY = int(os.getenv("LINE_API_RETRY", "2"))  # à¸ˆà¸³à¸™à¸§à¸™à¸„à¸£à¸±à¹‰à¸‡ retry à¹€à¸¡à¸·à¹ˆà¸­ timeout

line_bot_api = LineBotApi(CHANNEL_ACCESS_TOKEN, timeout=LINE_API_TIMEOUT)
handler = WebhookHandler(CHANNEL_SECRET)
app = Flask(__name__)

# ====== STATE ======
rooms = {}   # room_key -> state
users = {}   # uid -> {uid,cid,name,pictureUrl,credit}
nextCustomerId = 201


PLAY_HELP_TEXT = (
"à¸à¸•à¸´à¸à¸²à¸à¸²à¸£à¹€à¸¥à¹ˆà¸™\n"
"à¸•/1000 = à¹à¸—à¸‡à¸•à¹ˆà¸³ 1000 à¸šà¸²à¸—\n"
"à¸¢/1000 = à¹à¸—à¸‡à¸•à¹ˆà¸³ 1000 à¸šà¸²à¸—\n"
"à¸¥/1000 = à¹à¸—à¸‡à¸ªà¸¹à¸‡ 1000 à¸šà¸²à¸—\n"
"à¸ª/1000 = à¹à¸—à¸‡à¸ªà¸¹à¸‡ 1000 à¸šà¸²à¸—\n"
"à¸ªà¸²à¸¡à¸²à¸£à¸–à¹ƒà¸ªà¹ˆà¹€à¸„à¸£à¸·à¹ˆà¸­à¸‡à¸«à¸¡à¸²à¸¢ /\n"
"à¸«à¸£à¸·à¸­à¹„à¸¡à¹ˆà¹ƒà¸ªà¹ˆà¸à¹‡à¹„à¸”à¹‰ \n\n"
"âœ… à¸Šà¸™à¸°à¸«à¸±à¸ 5% (à¸ˆà¹ˆà¸²à¸¢à¸ªà¸¸à¸—à¸˜à¸´ 1:0.95)\n"
"â›” à¸•à¸ª à¸«à¸±à¸ 3%\n"
"â›” à¸•à¸ˆ à¸«à¸±à¸ 3%\n"
"â›” à¸¡ = à¹„à¸¡à¹ˆà¸«à¸±à¸\n\n"

"___________________\n\n"

"ðŸ‘‰ à¸£à¸±à¸šà¸ªà¸¹à¸‡à¸ªà¸¸à¸”à¸¢à¸±à¹‰à¸‡ 30,000 à¸•à¹ˆà¸­ 1 à¸šà¸±à¹‰à¸‡\n"
"ðŸ‘‰ à¸£à¸±à¸šà¸ªà¸¹à¸‡à¸ªà¸¸à¸”à¹„à¸¥à¹ˆ 50,000 à¸•à¹ˆà¸­ 1 à¸šà¸±à¹‰à¸‡\n"
"ðŸ‘‰ à¹à¸—à¸‡à¸‚à¸±à¹‰à¸™à¸•à¹ˆà¸³ à¸¢à¸±à¹‰à¸‡ 30-10,000 à¸•à¹ˆà¸­ \n"
"1à¸„à¸™\n"
"ðŸ«±ðŸ» à¹à¸—à¸‡à¸‚à¸±à¹‰à¸™à¸•à¹ˆà¸³ à¹„à¸¥à¹ˆ 30-10,000 à¸•à¹ˆà¸­ 1à¸„à¸™\n\n"
"ðŸ“¢ à¹€à¸žà¸´à¹ˆà¸¡ ID à¸•à¸±à¸§à¹€à¸­à¸‡ à¸žà¸´à¸¡à¸žà¹Œ ADD\n"
"ðŸ“¢ à¸”à¸¹à¸¢à¸­à¸”à¸šà¸±à¸à¸Šà¸µà¸•à¸±à¸§à¹€à¸­à¸‡ à¸à¸” C\n"
"ðŸ“¢ à¸¢à¸à¹€à¸¥à¸´à¸à¸à¸²à¸£à¹à¸—à¸‡ à¸à¸” X\n\n\n"
"***à¸«à¹‰à¸²à¸¡à¹€à¸§à¹‰à¸™à¸§à¸£à¸£à¸„ ***\n"
"ðŸ™à¸žà¸´à¸¡à¸žà¹Œà¸¢à¸­à¸”à¸à¸²à¸£à¹€à¸¥à¹ˆà¸™à¹ƒà¸«à¹‰à¸–à¸¹à¸à¸•à¹‰à¸­à¸‡à¸”à¹‰à¸§à¸¢à¸™à¸°à¸„à¸£à¸±à¸šðŸ™\n"
"à¸•à¸±à¸§à¸­à¸¢à¹ˆà¸²à¸‡:\n"
"à¸¥/1000 à¸ª/1000 à¸¥1000 à¸ª1000=à¹„à¸¥à¹ˆ\n"
"à¸¢/1000 à¸•/1000 à¸¢1000 à¸•1000=à¸¢à¸±à¹‰à¸‡\n"
"(à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¹€à¸§à¹‰à¸™à¸§à¸£à¸£à¸„)\n\n"
"à¸«à¸¡à¸²à¸¢à¹€à¸«à¸•à¸¸ // ðŸ’¥à¸à¸£à¸“à¸µà¸­à¸­à¸à¸£à¸²à¸„à¸² à¸šà¸±à¹‰à¸‡à¹„à¸Ÿ à¸«à¸¥à¸±à¸‡à¸›à¸´à¸” à¸–à¸·à¸­à¸§à¹ˆà¸² à¸ˆà¸²à¸§à¸—à¸¸à¸à¸£à¸“à¸µ\n"
"à¹à¸¥à¸°à¸ªà¸™à¸²à¸¡à¸£à¸²à¸„à¸²à¸£à¸¹à¸” à¸—à¸²à¸‡à¸à¸¥à¸¸à¹ˆà¸¡à¸ˆà¸°à¹„à¸¡à¹ˆà¹€à¸›à¸´à¸”à¸£à¸²à¸„à¸² à¸ˆà¸²à¸§à¸—à¸¸à¸à¸à¸£à¸“à¸µ ðŸ’¥"
)

PLAY_HELP_COMMANDS = {
    "à¸§à¸´à¸˜à¸µà¹€à¸¥à¹ˆà¸™",
    "à¹€à¸¥à¹ˆà¸™à¸¢à¸±à¸‡à¹„à¸‡",
    "à¹€à¸¥à¹ˆà¸™à¹„à¸‡",
    "à¸§à¸´à¸˜à¸µà¸à¸²à¸£à¹€à¸¥à¹ˆà¸™",
    "à¹€à¸¥à¹ˆà¸™à¹à¸šà¸šà¹ƒà¸”",
}

# ===== Debounced Saver =====
_save_event = threading.Event()

def _save_users_snapshot():
    with with_users_lock():
        payload = {"nextCustomerId": nextCustomerId, "users": users}
    _atomic_write_json(USERS_JSON, payload)

def _persist_worker():
    while True:
        _save_event.wait()
        time.sleep(0.35)  # à¸£à¸§à¸¡à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸ à¸²à¸¢à¹ƒà¸™ 350ms à¸à¹ˆà¸­à¸™à¹€à¸‚à¸µà¸¢à¸™
        _save_users_snapshot()
        _save_event.clear()

threading.Thread(target=_persist_worker, daemon=True).start()


# à¹‚à¸«à¸¥à¸”à¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¸¥à¸¹à¸à¸„à¹‰à¸²+à¹€à¸„à¸£à¸”à¸´à¸•à¸ˆà¸²à¸à¸”à¸´à¸ªà¸à¹Œ (à¸–à¹‰à¸²à¸¡à¸µ)
load_users_persist()


# ====== AUTO DELETE: à¸¥à¸šà¹„à¸Ÿà¸¥à¹Œ Backup_round à¹€à¸¡à¸·à¹ˆà¸­à¸„à¸£à¸š 1 à¸§à¸±à¸™ à¹à¸šà¸šà¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¹€à¸Šà¹‡à¸„à¸—à¸¸à¸à¸Šà¸±à¹ˆà¸§à¹‚à¸¡à¸‡ ======
# à¸§à¸´à¸˜à¸µà¸—à¸³à¸‡à¸²à¸™:
# - à¸•à¸­à¸™à¸ªà¸£à¹‰à¸²à¸‡à¹„à¸Ÿà¸¥à¹Œ backup_round_*.json à¸ˆà¸°à¸•à¸±à¹‰à¸‡ Timer à¹ƒà¸«à¹‰à¸¥à¸šà¹„à¸Ÿà¸¥à¹Œà¸™à¸±à¹‰à¸™à¸«à¸¥à¸±à¸‡à¸„à¸£à¸š 24 à¸Šà¸±à¹ˆà¸§à¹‚à¸¡à¸‡à¸žà¸­à¸”à¸µ
# - à¸•à¸­à¸™à¹€à¸›à¸´à¸”à¸šà¸­à¸— à¸ˆà¸°à¸ªà¹à¸à¸™à¹„à¸Ÿà¸¥à¹Œ backup_round à¸—à¸µà¹ˆà¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆ 1 à¸„à¸£à¸±à¹‰à¸‡ à¹à¸¥à¹‰à¸§à¸•à¸±à¹‰à¸‡à¹€à¸§à¸¥à¸²à¸¥à¸šà¸•à¸²à¸¡à¸­à¸²à¸¢à¸¸à¹„à¸Ÿà¸¥à¹Œà¸—à¸µà¹ˆà¹€à¸«à¸¥à¸·à¸­
# - à¹„à¸¡à¹ˆà¸¡à¸µ worker à¹€à¸Šà¹‡à¸„à¸‹à¹‰à¸³à¸—à¸¸à¸ 1 à¸Šà¸±à¹ˆà¸§à¹‚à¸¡à¸‡
BACKUP_ROUND_KEEP_SEC = int(os.getenv("BACKUP_ROUND_KEEP_SEC", str(24 * 60 * 60)))
BACKUP_ROUND_PREFIXES = ("backup_round", "backup-round")
_backup_round_timers = {}
_backup_round_timers_lock = threading.RLock()


def _is_backup_round_file(filename: str) -> bool:
    low = (filename or "").lower()
    return low.endswith(".json") and low.startswith(BACKUP_ROUND_PREFIXES)


def _delete_backup_round_file(path: str):
    """à¸¥à¸šà¹„à¸Ÿà¸¥à¹Œ backup_round 1 à¹„à¸Ÿà¸¥à¹Œ à¹€à¸¡à¸·à¹ˆà¸­à¸„à¸£à¸šà¹€à¸§à¸¥à¸² à¹‚à¸”à¸¢à¹„à¸¡à¹ˆà¹à¸•à¸°à¹„à¸Ÿà¸¥à¹Œà¸­à¸·à¹ˆà¸™à¹ƒà¸™ data"""
    try:
        filename = os.path.basename(path)
        if not _is_backup_round_file(filename):
            return

        if os.path.isfile(path):
            os.remove(path)
            app.logger.info("Deleted backup_round after 1 day: %s", filename)

    except FileNotFoundError:
        pass
    except Exception:
        app.logger.exception("delete backup_round failed: %s", path)
    finally:
        with _backup_round_timers_lock:
            _backup_round_timers.pop(path, None)


def schedule_backup_round_delete(path: str):
    """à¸•à¸±à¹‰à¸‡à¹€à¸§à¸¥à¸²à¸¥à¸šà¹„à¸Ÿà¸¥à¹Œ backup_round à¹€à¸¡à¸·à¹ˆà¸­à¸­à¸²à¸¢à¸¸à¸„à¸£à¸š 1 à¸§à¸±à¸™à¸žà¸­à¸”à¸µ"""
    try:
        if not path:
            return

        filename = os.path.basename(path)
        if not _is_backup_round_file(filename):
            return

        if not os.path.isfile(path):
            return

        age_sec = time.time() - os.path.getmtime(path)
        delay_sec = max(0, BACKUP_ROUND_KEEP_SEC - age_sec)

        # à¸–à¹‰à¸²à¹„à¸Ÿà¸¥à¹Œà¹€à¸à¸´à¸™ 1 à¸§à¸±à¸™à¹à¸¥à¹‰à¸§ à¹ƒà¸«à¹‰à¸¥à¸šà¸—à¸±à¸™à¸—à¸µ
        if delay_sec <= 0:
            _delete_backup_round_file(path)
            return

        with _backup_round_timers_lock:
            old_timer = _backup_round_timers.pop(path, None)
            if old_timer:
                old_timer.cancel()

            timer = threading.Timer(delay_sec, _delete_backup_round_file, args=(path,))
            timer.daemon = True
            _backup_round_timers[path] = timer
            timer.start()

        app.logger.info("Scheduled backup_round delete: %s in %.0f sec", filename, delay_sec)

    except Exception:
        app.logger.exception("schedule_backup_round_delete failed: %s", path)


def schedule_existing_backup_round_deletes():
    """à¸•à¸­à¸™à¹€à¸›à¸´à¸”à¸šà¸­à¸—: à¸•à¸±à¹‰à¸‡à¹€à¸§à¸¥à¸²à¸¥à¸š backup_round à¸—à¸µà¹ˆà¸¡à¸µà¸­à¸¢à¸¹à¹ˆà¹€à¸”à¸´à¸¡ 1 à¸„à¸£à¸±à¹‰à¸‡à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™"""
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        for filename in os.listdir(DATA_DIR):
            if not _is_backup_round_file(filename):
                continue
            schedule_backup_round_delete(os.path.join(DATA_DIR, filename))
    except Exception:
        app.logger.exception("schedule_existing_backup_round_deletes failed")


schedule_existing_backup_round_deletes()

# ====== ACCUMULATED METRICS (backoffice) ======
METRICS = {"profit_sum": 0, "loss_sum": 0}
def net_profit(): return METRICS["profit_sum"] - METRICS["loss_sum"]

def fmt(n: int) -> str: return f"{n:,}"

msgCache = {}
CACHE_TTL_SEC = 900

# --- Rounding policy helpers ---
def _round_refund(x: float) -> int:
    # à¹€à¸¥à¸·à¸­à¸à¹„à¸”à¹‰: floor = à¸›à¸±à¸”à¸¥à¸‡, ceil = à¸›à¸±à¸”à¸‚à¸¶à¹‰à¸™
    return floor(x)

def _round_profit(x: float) -> int:
    # à¸à¸³à¹„à¸£à¸à¹‡à¹ƒà¸Šà¹‰ policy à¹€à¸”à¸µà¸¢à¸§à¸à¸±à¸™à¹€à¸žà¸·à¹ˆà¸­à¸„à¸§à¸²à¸¡à¸„à¸‡à¹€à¸ªà¹‰à¸™à¸„à¸‡à¸§à¸²
    return floor(x)


# ====== RESULT DEFINITIONS ======
RESULT_DEFS = {
    # à¸›à¸à¸•à¸´: à¸à¸±à¹ˆà¸‡à¸Šà¸™à¸°à¸ˆà¹ˆà¸²à¸¢à¸à¸³à¹„à¸£à¸ªà¸¸à¸—à¸˜à¸´ PROFIT_RATE, à¸à¸±à¹ˆà¸‡à¹à¸žà¹‰à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡ (à¹à¸•à¹ˆà¹€à¸£à¸² â€œà¸•à¸±à¸”à¸•à¸­à¸™à¸§à¸²à¸‡à¸šà¸´à¸¥à¹à¸¥à¹‰à¸§â€ à¸ˆà¸¶à¸‡à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¸«à¸±à¸à¹€à¸žà¸´à¹ˆà¸¡à¸•à¸­à¸™à¸ªà¸£à¸¸à¸›)
    "à¸ª":  {"label": "à¸ªà¸¹à¸‡à¸Šà¸™à¸° (à¸ˆà¹ˆà¸²à¸¢ 1 : %.2f)" % PROFIT_RATE, "winner": "HI"},
    "à¸•":  {"label": "à¸•à¹ˆà¸³à¸Šà¸™à¸° (à¸ˆà¹ˆà¸²à¸¢ 1 : %.2f)" % PROFIT_RATE, "winner": "LO"},

    # à¸à¸¥à¸²à¸‡/à¸ˆà¸²à¸§/à¹€à¸ªà¸¡à¸­-à¸«à¸²à¸¢
    "à¸":  {"label": "à¸à¸¥à¸²à¸‡ (à¸«à¸±à¸ %.0f%%)" % (MIDDLE_FEE*100), "special": "MIDDLE_FEE"},
    "à¸ˆ":  {"label": "à¸ˆà¸²à¸§ (à¸„à¸·à¸™à¹€à¸•à¹‡à¸¡ à¹„à¸¡à¹ˆà¸«à¸±à¸)", "special": "DRAW_0"},
    "à¸¡":  {"label": "à¹€à¸ªà¸¡à¸­-à¸«à¸²à¸¢ (à¸„à¸·à¸™à¹€à¸•à¹‡à¸¡ à¹„à¸¡à¹ˆà¸«à¸±à¸)", "special": "DRAW_0"},

    # à¹€à¸„à¸ªà¸™à¹‚à¸¢à¸šà¸²à¸¢à¸žà¸´à¹€à¸¨à¸©
    "à¸•à¸ˆ": {"label": "à¸•à¹ˆà¸³à¹€à¸ªà¸¡à¸­ (à¸«à¸±à¸ %.0f%%) / à¸ªà¸¹à¸‡à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡" % (MIDDLE_FEE*100), "special": "LOW_DRAWFEE_HIGH_LOSE"},
    "à¸•à¸ª": {"label": "à¸•à¹ˆà¸³à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡ / à¸ªà¸¹à¸‡à¹€à¸ªà¸¡à¸­ (à¸«à¸±à¸ %.0f%%)" % (MIDDLE_FEE*100), "special": "LOW_LOSE_HIGH_DRAWFEE"},
}

def normalize_result_code(code: str) -> str:
    code = (code or "").strip()
    if code.startswith(("S", "s")) and len(code) >= 2:
        return code[1:].strip()
    return code

# ====== HELPERS ======
def room_key(src):
    return getattr(src, "group_id", None) or getattr(src, "room_id", None) or getattr(src, "user_id", None)

def in_group_or_room(src) -> bool:
    return bool(
        getattr(src, "group_id", None)
        or getattr(src, "room_id", None)
        or getattr(src, "user_id", None)
    )


def is_backoffice_group_id(gid): return gid in BACKOFFICE_GROUP_IDS

def start_state():
    return {
        "phase": "NONE",  # NONE | OPEN | PAUSED
        "pairNo": 0,
        "note": None,
        "pendingCode": None,
        "totals": {"HI": 0, "LO": 0},
        "bet_index": {},  # uid -> {uid,name,side,amount}
        "funds": {},      # uid -> à¸—à¸¸à¸™à¸£à¸­à¸šà¸™à¸µà¹‰
        "price": {"camp": None, "HI": (None, None), "LO": (None, None)},
        "escrow": {},     # à¹€à¸‡à¸´à¸™à¸—à¸µà¹ˆà¸–à¸¹à¸à¸«à¸±à¸à¸­à¸­à¸à¹„à¸›à¸—à¸±à¸™à¸—à¸µà¹€à¸¡à¸·à¹ˆà¸­à¸£à¸±à¸šà¸šà¸´à¸¥ uid -> amount
    }

# à¹à¸à¹‰à¹„à¸‚à¹ƒà¸™à¸Ÿà¸±à¸‡à¸à¹Œà¸Šà¸±à¸™ start_state()
def start_state():
    return {
        "phase": "NONE",  # NONE | OPEN | PAUSED
        "pairNo": 0,
        "note": None,
        "pendingCode": None,
        "totals": {"HI": 0, "LO": 0},
        "bet_index": {},  
        "funds": {},      
        "price": {"camp": None, "HI": (None, None), "LO": (None, None)},
        "escrow": {},
        "score_history": [],  # à¹€à¸à¹‡à¸šà¸›à¸£à¸°à¸§à¸±à¸•à¸´à¸œà¸¥à¸ªà¸à¸­à¸šà¸±à¹‰à¸‡à¹„à¸Ÿà¸§à¸±à¸™à¸™à¸µà¹‰
        "settling": False,
        "last_closed_pairNo": None,
        "last_settled_pairNo": None,
    }

_profile_cache = {}           # uid -> (display_name, picture_url, ts)
_PROFILE_CACHE_TTL = int(os.getenv("PROFILE_CACHE_TTL", "300"))  # 5 à¸™à¸²à¸—à¸µ (à¸›à¸£à¸±à¸šà¹ƒà¸™ .env à¹„à¸”à¹‰)

def get_profile_display(src, user_id):
    now = time.time()
    cached = _profile_cache.get(user_id)
    if cached and (now - cached[2]) < _PROFILE_CACHE_TTL:
        return cached[0], cached[1]
    try:
        if getattr(src, "group_id", None):
            p = line_bot_api.get_group_member_profile(src.group_id, user_id)
        elif getattr(src, "room_id", None):
            p = line_bot_api.get_room_member_profile(src.room_id, user_id)
        else:
            p = line_bot_api.get_profile(user_id)
        result = (p.display_name, p.picture_url)
    except Exception:
        result = ("à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™", None)
    _profile_cache[user_id] = (*result, now)
    return result

def parse_bet(text):
    m = R_PARSE_BET.match(text)
    if not m: return None
    ch = m.group(1).lower()
    amount = int(m.group(2))
    side = "HI" if ch in ("à¸¥", "à¸ª") else "LO"
    return {"side": side, "amount": amount}


def get_user_bet(state, uid): return state["bet_index"].get(uid)
def user_stake_this_round(state, uid): return get_user_bet(state, uid)["amount"] if get_user_bet(state, uid) else 0

def user_fund_remain(state, uid):
    u = users.get(uid)
    if not u: return 0
    return max(u.get("credit", 0), 0)

# ==== 1 à¸šà¸´à¸¥/à¸£à¸­à¸š + à¸à¸±à¸™à¹à¸—à¸‡à¸ªà¸§à¸™ ====
def can_bet(state, uid, side, amount):
    if state["phase"] != "OPEN":
        return (False, "à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¹€à¸›à¸´à¸”à¸£à¸­à¸š")

    existing = get_user_bet(state, uid)
    if existing:
        exist_side_th = "à¸ªà¸¹à¸‡" if existing["side"] == "HI" else "à¸•à¹ˆà¸³"
        if side != existing["side"]:
            return (False, f"âŒ à¸«à¹‰à¸²à¸¡à¹à¸—à¸‡à¸ªà¸§à¸™ â€” à¸„à¸¸à¸“à¸¡à¸µà¸šà¸´à¸¥à¹€à¸”à¸´à¸¡: {exist_side_th} {fmt(existing['amount'])}  (à¸žà¸´à¸¡à¸žà¹Œ X à¹€à¸žà¸·à¹ˆà¸­à¸¢à¸à¹€à¸¥à¸´à¸à¸à¹ˆà¸­à¸™)")
        else:
            return (False, f"âŒ à¸ˆà¸³à¸à¸±à¸” 1 à¸šà¸´à¸¥/à¸£à¸­à¸š â€” à¸„à¸¸à¸“à¸¡à¸µà¸šà¸´à¸¥ {exist_side_th} {fmt(existing['amount'])} à¸­à¸¢à¸¹à¹ˆà¹à¸¥à¹‰à¸§  (à¸žà¸´à¸¡à¸žà¹Œ X à¹€à¸žà¸·à¹ˆà¸­à¸¢à¸à¹€à¸¥à¸´à¸à¸à¹ˆà¸­à¸™)")

    if amount < MIN_BET:
        return (False, f"à¸‚à¸±à¹‰à¸™à¸•à¹ˆà¸³ {MIN_BET}")
    if amount > MAX_BET:
        return (False, f"à¸ªà¸¹à¸‡à¸ªà¸¸à¸” {MAX_BET}")

    remain = user_fund_remain(state, uid)
    if remain < amount:
        return (False, f"à¸—à¸¸à¸™à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­à¹„à¸¡à¹ˆà¸žà¸­ (à¸¡à¸µ {fmt(remain)})")

    if amount > USER_SIDE_CAP[side]:
        side_th = "à¸ªà¸¹à¸‡" if side == "HI" else "à¸•à¹ˆà¸³"
        return (False, f"à¸à¸±à¹ˆà¸‡{side_th} à¸•à¹ˆà¸­à¸„à¸™à¹€à¸à¸´à¸™ {fmt(USER_SIDE_CAP[side])}")

    # âœ… à¹€à¸Šà¹‡à¸„à¹€à¸žà¸”à¸²à¸™à¸•à¹ˆà¸­à¸à¸±à¹ˆà¸‡ (à¸¢à¹‰à¸²à¸¢à¸­à¸­à¸à¸¡à¸²à¹ƒà¸«à¹‰à¸­à¸¢à¸¹à¹ˆà¸™à¸­à¸ if à¸”à¹‰à¸²à¸™à¸šà¸™)
    if state["totals"][side] + amount > SIDE_CAP[side]:
        side_th = "à¸ªà¸¹à¸‡" if side == "HI" else "à¸•à¹ˆà¸³"
        side_cap = SIDE_CAP[side]
        side_total = state["totals"][side]
        remain_to_cap = max(side_cap - side_total, 0)
        return (
            False,
            f"âŒà¸£à¸±à¸šà¸šà¸´à¸¥à¹„à¸¡à¹ˆà¹„à¸”à¹‰âŒ: à¸à¸±à¹ˆà¸‡{side_th} à¹€à¸•à¹‡à¸¡ {fmt(side_cap)} - à¹€à¸«à¸¥à¸·à¸­à¸£à¸±à¸šà¹„à¸”à¹‰à¸­à¸µà¸ {fmt(remain_to_cap)}"
        )

    # âœ… à¹€à¸Šà¹‡à¸„à¹€à¸žà¸”à¸²à¸™à¸£à¸§à¸¡à¸£à¸­à¸š + à¹à¸ˆà¹‰à¸‡à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­
    round_total = state["totals"]["HI"] + state["totals"]["LO"]
    if round_total + amount > ROUND_CAP:
        remain_round = max(ROUND_CAP - round_total, 0)
        return (False, f"âŒà¸£à¸±à¸šà¸šà¸´à¸¥à¹„à¸¡à¹ˆà¹„à¸”à¹‰âŒ: à¸£à¸­à¸šà¸™à¸µà¹‰à¹€à¸•à¹‡à¸¡ {fmt(ROUND_CAP)} - à¹€à¸«à¸¥à¸·à¸­à¸£à¸±à¸šà¹„à¸”à¹‰à¸­à¸µà¸ {fmt(remain_round)}")

    return (True, "")

# ==== mention helpers ====
def first_mentioned_uid(event):
    try:
        m = getattr(event.message, "mention", None)
        if not m: return None
        for me in (getattr(m, "mentionees", None) or []):
            uid = getattr(me, "user_id", None) or getattr(me, "userId", None)
            if uid and str(uid).lower() != "all":
                return uid
    except Exception:
        pass
    return None

def format_user_table(data):
    if not data:
        return "à¹„à¸¡à¹ˆà¸¡à¸µà¸‚à¹‰à¸­à¸¡à¸¹à¸¥"

    import re

    def clean_name(name):
        return re.sub(r'[^\w\sà¸-à¹™]', '', name or "")

    ID_W = 4
    NAME_W = 16
    CREDIT_W = 8

    header = f"{'ID':<{ID_W}} | {'à¸Šà¸·à¹ˆà¸­':<{NAME_W}} | {'à¹€à¸„à¸£à¸”à¸´à¸•':>{CREDIT_W}}"
    sep = "-" * len(header)

    lines = []
    lines.append("ðŸ“‹ à¸£à¸²à¸¢à¸Šà¸·à¹ˆà¸­à¸ªà¸¡à¸²à¸Šà¸´à¸")
    lines.append(sep)
    lines.append(header)
    lines.append(sep)

    total_credit = 0

    for u in data:
        cid = str(u.get("cid", ""))
        name = clean_name(u.get("name", ""))[:NAME_W]
        credit = u.get("credit", 0)

        total_credit += credit

        line = f"{cid:<{ID_W}} | {name:<{NAME_W}} | {credit:>{CREDIT_W},}"
        lines.append(line)

    lines.append(sep)

    # ===== à¸£à¸§à¸¡à¹€à¸„à¸£à¸”à¸´à¸• =====
    lines.append(f"ðŸ’° à¸£à¸§à¸¡à¹€à¸„à¸£à¸”à¸´à¸•à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”: {total_credit:,} à¸šà¸²à¸—")

    return "\n".join(lines)


# ====== FLEX ======
def flex_open(pair_no, note=None):
    body_contents = [
        {"type": "text", "text": "ðŸŽ¯ à¹€à¸£à¸´à¹ˆà¸¡à¹à¸—à¸‡à¹„à¸”à¹‰ ðŸŽ¯", "weight": "bold", "size": "xxl", "align": "center", "color": "#22C55E"},
        {"type": "text", "text": "à¸šà¸­à¸—à¹„à¸¡à¹ˆà¸ˆà¸±à¸š à¹„à¸¡à¹ˆà¹„à¸”à¹‰à¹€à¸ªà¸µà¸¢ à¸—à¸¸à¸à¸à¸£à¸“à¸µ â€¢", "size": "md", "align": "center", "color": "#EF4444"},
        {"type": "separator", "margin": "lg", "color": "#4B5563"},
        {"type": "text", "text": f"à¸£à¸­à¸šà¸—à¸µà¹ˆ {pair_no}", "align": "center", "size": "lg", "weight": "bold", "color": "#FFFFFF"},
        {"type": "text", "text": f"à¸£à¸­à¹à¸­à¸”à¸¡à¸´à¸™à¸­à¸­à¸à¸£à¸²à¸„à¸²à¸ªà¸±à¸à¸„à¸£à¸¹à¹ˆ", "align": "center", "size": "lg", "weight": "bold", "color": "#DB0A0A"},
    ]
    if note:
        body_contents += [
            {"type": "separator", "margin": "lg", "color": "#4B5563"},
            {"type": "text", "text": f"à¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢: {note}", "size": "md", "wrap": True, "align": "center", "color": "#FACC15"},
        ]

    return FlexSendMessage(
        alt_text=f"à¹€à¸£à¸´à¹ˆà¸¡à¹à¸—à¸‡à¹„à¸”à¹‰ à¸£à¸­à¸šà¸—à¸µà¹ˆ {pair_no}",
        contents={
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "0px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#22C55E",
                        "cornerRadius": "20px",
                        "paddingAll": "3px",
                        "contents": [
                            {
                                "type": "box",
                                "layout": "vertical",
                                "backgroundColor": "#111827",
                                "cornerRadius": "16px",
                                "paddingAll": "3px",
                                "contents": [
                                    {
                                        "type": "box",
                                        "layout": "vertical",
                                        "backgroundColor": "#1F2937",
                                        "cornerRadius": "12px",
                                        "paddingAll": "20px",
                                        "contents": body_contents
                                    }
                                ]
                            }
                        ]
                    }
                ]
            }
        }
    )



def flex_resume(pair_no: int, camp: str):
    return FlexSendMessage(
        alt_text=f"à¸à¸¥à¸±à¸šà¸¡à¸²à¹€à¸›à¸´à¸”à¸£à¸­à¸š {pair_no}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#0B1220"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "14px",
                "spacing": "12px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#16A34A",
                        "cornerRadius": "12px",
                        "paddingAll": "12px",
                        "contents": [
                            {
                                "type": "text",
                                "text": "à¹€à¸›à¸´à¸”à¹ƒà¸«à¹‰à¹€à¸¥à¹ˆà¸™à¸­à¸µà¸à¸£à¸­à¸š!!",
                                "weight": "bold",
                                "size": "lg",
                                "align": "center",
                                "color": "#FFFFFF"
                            },
                            {
                                "type": "text",
                                "text": f"à¸£à¸­à¸šà¸—à¸µà¹ˆ {pair_no}",
                                "size": "sm",
                                "align": "center",
                                "color": "#E5E7EB"
                            }
                        ]
                    },
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#111827",
                        "cornerRadius": "12px",
                        "paddingAll": "12px",
                        "spacing": "8px",
                        "contents": [
                            {
                                "type": "text",
                                "text": f"à¸„à¹ˆà¸²à¸¢: {camp}",
                                "size": "md",
                                "weight": "bold",
                                "color": "#FACC15",
                                "wrap": True
                            },
                            {"type": "separator", "color": "#334155"},
                            {
                                "type": "text",
                                "text": "à¸®à¹ˆà¸³à¸¡à¸±à¸™à¹€à¸‚à¹‰à¸²à¹„à¸›à¸„à¸±à¸à¹† à¸«à¸¡à¸²à¸™à¹†à¸™à¸°à¸ªà¸¡à¸²à¸Šà¸´à¸",
                                "size": "sm",
                                "color": "#CBD5E1",
                                "wrap": True
                            },
                            {
                                "type": "text",
                                "text": "à¸¢à¸à¹€à¸¥à¸´à¸à¸šà¸´à¸¥à¸žà¸´à¸¡à¸žà¹Œ X â€¢ à¸”à¸¹à¸šà¸±à¸•à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸à¸žà¸´à¸¡à¸žà¹Œ C",
                                "size": "xs",
                                "color": "#94A3B8",
                                "wrap": True
                            }
                        ]
                    }
                ]
            }
        }
    )


def flex_open_with_prices(pair_no, camp, hi_min, hi_max, lo_min, lo_max):
    hi_txt = f"{hi_min}-{hi_max}" if hi_min is not None and hi_max is not None else "-"
    lo_txt = f"{lo_min}-{lo_max}" if lo_min is not None and lo_max is not None else "-"

    return FlexSendMessage(
        alt_text=f"à¹€à¸£à¸´à¹ˆà¸¡à¹à¸—à¸‡à¹„à¸”à¹‰ à¸£à¸­à¸šà¸—à¸µà¹ˆ {pair_no}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#D1FAE5"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "sm",
                "paddingAll": "14px",
                "contents": [
                    {"type": "text", "text": "ðŸŽ¯ à¸£à¸²à¸„à¸²à¸¡à¸²à¹à¸¥à¹‰à¸§à¸§!! ðŸŽ¯", "weight": "bold", "size": "xl", "align": "center", "color": "#16A34A"},
                    {"type": "text", "text": "à¸šà¸­à¸—à¹„à¸¡à¹ˆà¸ˆà¸±à¸š à¹„à¸¡à¹ˆà¹„à¸”à¹‰à¹€à¸ªà¸µà¸¢ à¸—à¸¸à¸à¸à¸£à¸“à¸µ", "size": "sm", "align": "center", "color": "#EF4444"},
                    {"type": "separator", "margin": "md"},
                    {"type": "text", "text": f"ðŸŸ¢ðŸš€à¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢ :  {camp}", "size": "md", "weight": "bold", "wrap": True},
                    {"type": "text", "text": f"ðŸŸ¢à¹„à¸¥à¹ˆà¸£à¸²à¸„à¸²à¸™à¸µà¹‰ðŸŸ¢{hi_txt}ðŸŸ¢", "size": "lg", "weight": "bold"},
                    {"type": "separator", "margin": "md"},
                    {"type": "text", "text": "ðŸ¡ à¸£à¸²à¸„à¸²à¸šà¸±à¹‰à¸‡à¹„à¸Ÿà¹à¸­à¸”à¸¡à¸´à¸™à¸à¸³à¸«à¸™à¸”à¸•à¸²à¸¡à¸„à¸§à¸²à¸¡à¹€à¸«à¸¡à¸²à¸°à¸ªà¸¡", "size": "sm", "wrap": True},
                    {"type": "text", "text": "ðŸ¡ à¸­à¸­à¸à¸£à¸²à¸„à¸²à¸šà¸±à¹‰à¸‡à¹„à¸Ÿà¸«à¸¥à¸±à¸‡à¸›à¸´à¸” à¸–à¸·à¸­à¸§à¹ˆà¸²à¸ˆà¸²à¸§à¸—à¸¸à¸à¸à¸£à¸“à¸µ", "size": "sm", "wrap": True},
                    {"type": "text", "text": f"ðŸ‘‰ à¹à¸—à¸‡à¸‚à¸±à¹‰à¸™à¸•à¹ˆà¸³ {MIN_BET} - {fmt(MAX_BET)} à¸šà¸²à¸—/à¸„à¸™/à¸£à¸­à¸š", "size": "sm"},
                    {"type": "text", "text": f"ðŸ‘‰ à¸£à¸§à¸¡à¸•à¹ˆà¸­à¸à¸±à¹ˆà¸‡/à¸£à¸­à¸š: à¸ªà¸¹à¸‡ {fmt(SIDE_CAP['HI'])} â€¢ à¸•à¹ˆà¸³ {fmt(SIDE_CAP['LO'])}", "size": "sm"},
                    {"type": "text", "text": f"ðŸ‘‰ à¸­à¸±à¸•à¸£à¸²à¸ˆà¹ˆà¸²à¸¢à¸Šà¸™à¸° 1 : {PROFIT_RATE:.2f}", "size": "sm"},
                    {"type": "text", "text": f"ðŸ‘‰ à¸­à¸­à¸à¸à¸¥à¸²à¸‡à¸«à¸±à¸ {int(MIDDLE_FEE*100)}%", "size": "sm"},
                    {"type": "text", "text": "ðŸ‘‰ à¸‹à¸¸à¹à¸•à¸à¸„à¸²à¸–à¸²à¸™,à¸«à¸²à¸¢ = à¸ˆà¸²à¸§", "size": "sm"},
                    {"type": "separator", "margin": "md"},
                    {"type": "text", "text": f"ðŸŸ¢ðŸš€à¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢ :  {camp}", "size": "md", "weight": "bold", "wrap": True},
                    {"type": "text", "text": f"ðŸ”´à¸¢à¸±à¹‰à¸‡à¸£à¸²à¸„à¸²à¸™à¸µà¹‰ðŸ”´{lo_txt}ðŸ”´", "size": "lg", "weight": "bold"},
                    {"type": "separator", "margin": "md"},
                    {"type": "text", "text": "ðŸ“¢ à¸¢à¸à¹€à¸¥à¸´à¸à¸à¸²à¸£à¹à¸—à¸‡ à¸à¸” X", "size": "sm"},
                    {"type": "text", "text": "ðŸ“¢ à¸”à¸¹à¸¢à¸­à¸”à¸«à¸™à¹‰à¸²à¸šà¸±à¸à¸Šà¸µà¸•à¸±à¸§à¹€à¸­à¸‡ à¸à¸” C", "size": "sm"},
                    {"type": "text", "text": "â€¼ï¸à¸à¸£à¸“à¸µà¸«à¸™à¹‰à¸²à¸à¸²à¸™à¸£à¸²à¸„à¸²à¸£à¸¹à¸”à¸œà¸´à¸”à¸›à¸à¸•à¸´à¹à¸­à¸”à¸¡à¸´à¸™à¸ªà¸²à¸¡à¸²à¸£à¸–à¹à¸ˆà¹‰à¸‡à¸¢à¸à¹€à¸¥à¸´à¸à¹„à¸”à¹‰â€¼", "size": "xs", "wrap": True},
                ]
            }
        }
    )

def flex_close_notice(pair_no):
    # à¸à¸²à¸£à¹Œà¸”à¹à¸ˆà¹‰à¸‡à¸«à¸¢à¸¸à¸”à¹à¸—à¸‡ (à¸›à¸´à¸”à¸£à¸­à¸š) à¹‚à¸—à¸™à¹€à¸”à¸µà¸¢à¸§à¸à¸±à¸šà¸•à¸±à¸§à¸­à¸¢à¹ˆà¸²à¸‡
    return FlexSendMessage(
        alt_text=f"à¸›à¸´à¸”à¸£à¸­à¸š #{pair_no}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#E5F0FF"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "md",
                "paddingAll": "16px",
                "contents": [
                    {"type": "text", "text": f"à¸›à¸´à¸”à¸£à¸­à¸š #{pair_no}", "weight": "bold",
                     "size": "xl", "align": "center", "color": "#1F2937"},
                    {"type": "box", "layout": "vertical", "backgroundColor": "#111827",
                     "cornerRadius": "12px", "paddingAll": "14px", "contents": [
                         {"type": "text", "text": "à¸«à¸¢à¸¸à¸”à¹à¸—à¸‡", "weight": "bold",
                          "size": "xxl", "align": "center", "color": "#EF4444"},
                         {"type": "text", "text": "à¸šà¸­à¸—à¹„à¸¡à¹ˆà¸ˆà¸±à¸š à¹„à¸¡à¹ˆà¹„à¸”à¹‰à¹€à¸ªà¸µà¸¢ à¸—à¸¸à¸à¸à¸£à¸“à¸µ",
                          "size": "md", "align": "center", "color": "#FDE68A"}
                     ]},
                    {"type": "text",
                     "text": "à¸£à¸°à¸šà¸šà¸›à¸´à¸”à¸£à¸±à¸šà¸šà¸´à¸¥à¹à¸¥à¹‰à¸§ à¸à¸£à¸¸à¸“à¸²à¸£à¸­à¸ªà¸£à¸¸à¸›à¸œà¸¥/à¸›à¸£à¸°à¸à¸²à¸¨à¸£à¸²à¸„à¸²à¸–à¸±à¸”à¹„à¸›",
                     "size": "sm", "align": "center", "wrap": True, "color": "#374151"}
                ]
            }
        }
    )

def flex_pause_notice(pair_no: int, camp: str):
    """à¸à¸²à¸£à¹Œà¸”à¹à¸ˆà¹‰à¸‡ 'à¸žà¸±à¸à¸£à¸­à¸šà¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§' à¸žà¸£à¹‰à¸­à¸¡à¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢"""
    if not camp:
        camp = "à¹„à¸¡à¹ˆà¸£à¸°à¸šà¸¸à¸„à¹ˆà¸²à¸¢"
    return FlexSendMessage(
        alt_text=f"à¸žà¸±à¸à¸£à¸­à¸šà¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§ #{pair_no}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#FFF7ED"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "md",
                "paddingAll": "16px",
                "contents": [
                    {
                        "type": "text",
                        "text": f"à¸«à¸¢à¸¸à¸”à¹à¸—à¸‡à¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§ #{pair_no}",
                        "weight": "bold",
                        "size": "xl",
                        "align": "center",
                        "color": "#1F2937"
                    },
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#111827",
                        "cornerRadius": "12px",
                        "paddingAll": "14px",
                        "contents": [
                            {
                                "type": "text",
                                "text": "â¸ï¸ à¸›à¸´à¸”à¸£à¸±à¸šà¸šà¸´à¸¥à¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§",
                                "weight": "bold",
                                "size": "lg",
                                "align": "center",
                                "color": "#F59E0B"
                            },
                            {
                                "type": "text",
                                "text": f"à¸„à¹ˆà¸²à¸¢ {camp} à¸£à¸­à¹à¸­à¸”à¸¡à¸´à¸™à¹€à¸›à¸´à¸”à¸­à¸µà¸à¸£à¸­à¸š",
                                "size": "sm",
                                "align": "center",
                                "color": "#FDE68A"
                            }
                        ]
                    },
                    {
                        "type": "text",
                        "text": "à¸«à¸¢à¸¸à¸”à¹à¸¥à¹‰à¸§à¸ˆà¸°à¹„à¸¡à¹ˆà¸ªà¸²à¸¡à¸²à¸£à¸–à¹à¸—à¸‡à¸«à¸£à¸·à¸­à¸¢à¸à¹€à¸¥à¸´à¸à¹„à¸”à¹‰ à¸£à¸­à¹à¸­à¸”à¸¡à¸´à¸™à¹€à¸›à¸´à¸”à¸­à¸µà¸à¸£à¸­à¸š",
                        "size": "xs",
                        "align": "center",
                        "wrap": True,
                        "color": "#6B7280"
                    }
                ]
            }
        }
    )



def flex_customer_card(st, user):
    """
    à¸à¸²à¸£à¹Œà¸”à¸ªà¸¡à¸²à¸Šà¸´à¸à¹à¸šà¸šà¹€à¸£à¸µà¸¢à¸šà¸‡à¹ˆà¸²à¸¢ à¹‚à¸—à¸™à¸ªà¸§à¹ˆà¸²à¸‡ à¹€à¸«à¸¡à¸·à¸­à¸™à¸•à¸±à¸§à¸­à¸¢à¹ˆà¸²à¸‡à¹ƒà¸™à¸£à¸¹à¸›
    à¹à¸ªà¸”à¸‡: à¸£à¸¹à¸› â€¢ ID â€¢ à¸Šà¸·à¹ˆà¸­ â€¢ à¹€à¸„à¸£à¸”à¸´à¸•à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­ â€¢ à¸£à¸²à¸¢à¸à¸²à¸£à¹€à¸¥à¹ˆà¸™ (à¸–à¹‰à¸²à¸¡à¸µ)
    """
    # à¸à¸±à¸™à¸à¸£à¸“à¸µà¹€à¸£à¸µà¸¢à¸à¸à¸²à¸£à¹Œà¸”à¸à¹ˆà¸­à¸™à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰ ADD / à¹„à¸¡à¹ˆà¸¡à¸µà¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¹ƒà¸™ users
    if not user:
        return TextSendMessage(text="à¸à¸£à¸¸à¸“à¸²à¸žà¸´à¸¡à¸žà¹Œ add à¹€à¸žà¸·à¹ˆà¸­à¸£à¸±à¸šà¹„à¸­à¸”à¸µà¸à¹ˆà¸­à¸™")

    uid = user["uid"]
    cid = user["cid"]
    name = user.get("name", "à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™")
    picture = user.get("pictureUrl") or "https://via.placeholder.com/48"
    credit_total = int(user.get("credit", 0) or 0)

    bet = get_user_bet(st, uid)
    have_bet = bet is not None
    side_th = "à¸ªà¸¹à¸‡" if (bet and bet["side"] == "HI") else ("à¸•à¹ˆà¸³" if bet else "")
    stake_used = int(bet["amount"]) if bet else 0

    # à¸ªà¸µà¸•à¸²à¸¡à¸à¸±à¹ˆà¸‡
    side_color = "#3B82F6" if side_th == "à¸ªà¸¹à¸‡" else "#EF4444"

    # à¹à¸–à¸šà¸ªà¸–à¸²à¸™à¸° (progress look) à¸„à¸§à¸²à¸¡à¸¢à¸²à¸§à¸•à¸²à¸¡à¸ªà¸±à¸”à¸ªà¹ˆà¸§à¸™ (à¸›à¸£à¸±à¸šà¹„à¸”à¹‰)
    # à¸«à¸¡à¸²à¸¢à¹€à¸«à¸•à¸¸: Flex à¹„à¸¡à¹ˆà¸¡à¸µ progress à¸ˆà¸£à¸´à¸‡ à¹† à¹ƒà¸Šà¹‰à¸à¸¥à¹ˆà¸­à¸‡à¸ªà¸­à¸‡à¸Šà¸±à¹‰à¸™à¹€à¸¥à¸µà¸¢à¸™à¹à¸šà¸š
    max_bar = max(stake_used, 1)
    filled_flex = 8 if have_bet else 0
    empty_flex = (12 - filled_flex) if have_bet else 12

    # à¸ªà¹ˆà¸§à¸™à¸«à¸±à¸§: à¹‚à¸›à¸£à¹„à¸Ÿà¸¥à¹Œ + ID/à¸Šà¸·à¹ˆà¸­ + à¹€à¸„à¸£à¸”à¸´à¸•à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­
    header = {
        "type": "box", "layout": "horizontal", "spacing": "12px",
        "contents": [
            {
                "type": "image", "url": picture, "size": "48px",
                "aspectMode": "cover", "aspectRatio": "1:1",
                "cornerRadius": "10px"
            },
            {
                "type": "box", "layout": "vertical", "flex": 7, "spacing": "2px",
                "contents": [
                    {
                        "type": "text",
                        "text": f"ID : {cid} {name}",
                        "weight": "bold",
                        "size": "md",
                        "color": "#111827",
                        "wrap": True,
                        "maxLines": 2
                    },
                    {
                        "type": "text",
                        "text": f"à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­ {fmt(credit_total)} à¸š.",
                        "size": "sm",
                        "color": "#6B7280"
                    }
                ]
            }
        ]
    }

    # à¸à¸¥à¹ˆà¸­à¸‡ "à¸£à¸²à¸¢à¸à¸²à¸£à¹€à¸¥à¹ˆà¸™" à¸–à¹‰à¸²à¸¡à¸µà¸šà¸´à¸¥
    bet_block = {
        "type": "box", "layout": "vertical", "spacing": "6px",
        "contents": [
            # à¹à¸–à¸§à¸«à¸±à¸§à¸‚à¹‰à¸­ + à¸ˆà¸³à¸™à¸§à¸™
            {
                "type": "box", "layout": "horizontal", "contents": [
                    {
                        "type": "text",
                        "text": side_th or "à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¹„à¸”à¹‰à¹€à¸”à¸´à¸¡à¸žà¸±à¸™",
                        "weight": "bold",
                        "size": "sm",
                        "color": "#111827",
                        "flex": 7
                    },
                    {
                        "type": "text",
                        "text": f"{fmt(stake_used)} à¸š." if have_bet else "",
                        "size": "sm",
                        "align": "end",
                        "color": "#111827",
                        "flex": 5
                    }
                ]
            },
            # à¹à¸–à¸šà¸ªà¸–à¸²à¸™à¸°
            {
                "type": "box", "layout": "horizontal",
                "backgroundColor": "#E5E7EB",
                "height": "10px",
                "cornerRadius": "10px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": side_color,
                        "cornerRadius": "10px",
                        "contents": [],
                        "flex": filled_flex
                    },
                    {"type": "filler", "flex": empty_flex}
                ]
            },
            # à¸šà¸£à¸£à¸—à¸±à¸”à¸«à¸±à¸à¸¥à¹ˆà¸§à¸‡à¸«à¸™à¹‰à¸² + à¹€à¸„à¸£à¸”à¸´à¸•à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­ (à¸ªà¹„à¸•à¸¥à¹Œà¸ à¸²à¸žà¸•à¸±à¸§à¸­à¸¢à¹ˆà¸²à¸‡)
            {
                "type": "box", "layout": "horizontal", "contents": [
                    {
                        "type": "text",
                        "text": f"à¸«à¸±à¸à¸¥à¹ˆà¸§à¸‡à¸«à¸™à¹‰à¸² -{fmt(stake_used)}" if have_bet else "",
                        "size": "xs",
                        "color": "#6B7280",
                        "flex": 7
                    },
                    {
                        "type": "text",
                        "text": f"à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­ {fmt(credit_total)} à¸š.",
                        "size": "xs",
                        "color": "#6B7280",
                        "align": "end",
                        "flex": 5
                    }
                ]
            }
        ]
    }

    # à¸–à¹‰à¸²à¹„à¸¡à¹ˆà¸¡à¸µà¸šà¸´à¸¥ à¹ƒà¸«à¹‰à¹à¸ªà¸”à¸‡à¸šà¸£à¸£à¸—à¸±à¸” â€œà¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸à¸²à¸£à¹€à¸”à¸´à¸¡à¸žà¸±à¸™â€
    if not have_bet:
        bet_block = {
            "type": "text",
            "text": "à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸à¸²à¸£à¹€à¸”à¸´à¸¡à¸žà¸±à¸™à¹ƒà¸™à¸£à¸­à¸šà¸™à¸µà¹‰",
            "size": "sm",
            "color": "#6B7280",
            "wrap": True
        }

    return FlexSendMessage(
        alt_text=f"ID {cid} â€” à¸à¸²à¸£à¹Œà¸”à¸ªà¸¡à¸²à¸Šà¸´à¸",
        contents={
            "type": "bubble",
            "size": "mega",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "12px",
                "backgroundColor": "#F3F4F6",   # à¹€à¸—à¸²à¸­à¹ˆà¸­à¸™à¹€à¸«à¸¡à¸·à¸­à¸™à¹à¸Šà¸•à¸•à¸±à¸§à¸­à¸¢à¹ˆà¸²à¸‡
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "cornerRadius": "16px",
                        "paddingAll": "12px",
                        "backgroundColor": "#FFFFFF",
                        "contents": [
                            header,
                            {"type": "box", "layout": "vertical", "margin": "md", "spacing": "8px",
                             "contents": [
                                 {"type": "separator", "color": "#E5E7EB"},
                                 bet_block
                             ]}
                        ]
                    }
                ]
            }
        }
    )


def text_bank():
    return TextSendMessage(
        text=(
            "ðŸ“Œ à¹€à¸‹à¸´à¹‰à¸‡Â®à¸šà¸±à¹‰à¸‡à¹„à¸Ÿà¸­à¸´à¸ªà¸²à¸™ V2\n\n"
            "âš ï¸à¹à¸ˆà¹‰à¸‡à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µà¸à¸²à¸âš ï¸\n\n"
            "ðŸ³ï¸ 020253012700  \n"
            "ðŸ’° à¸­à¸­à¸¡à¸ªà¸´à¸™\n"
            "ðŸ’³ à¸§à¸£à¸£à¸“à¸§à¸´à¹„à¸¥  à¸Šà¸²à¹€à¸¡à¸·à¸­à¸‡à¸à¸¸à¸¥\n\n"
            "ðŸ“Œ à¹€à¸žà¸·à¹ˆà¸­à¸›à¹‰à¸­à¸‡à¸à¸±à¸™à¸¡à¸´à¸ˆà¸‰à¸²à¸Šà¸µà¸ž à¸Šà¸·à¹ˆà¸­à¸œà¸¹à¹‰à¸à¸²à¸-à¸–à¸­à¸™ à¸•à¹‰à¸­à¸‡à¹€à¸›à¹‡à¸™à¸Šà¸·à¹ˆà¸­à¹€à¸”à¸µà¸¢à¸§à¸à¸±à¸™à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™âš ï¸\n"
            "ðŸ“Œ à¸à¸” C à¸”à¸¹à¹„à¸­à¸”à¸µà¸•à¸±à¸§à¹€à¸­à¸‡à¸ªà¹ˆà¸‡à¹ƒà¸«à¹‰à¹à¸­à¸”à¸¡à¸´à¸™à¹„à¸”à¹‰à¹€à¸¥à¸¢\n"
        )
    )


def flex_backoffice_button(url: str, label: str = "à¹€à¸›à¸´à¸”à¸«à¸™à¹‰à¸²à¸à¸²à¸à¹€à¸‡à¸´à¸™"):
    """à¸›à¸¸à¹ˆà¸¡ Flex à¸ªà¸³à¸«à¸£à¸±à¸šà¹€à¸›à¸´à¸”à¸«à¸™à¹‰à¸²à¹à¸ˆà¹‰à¸‡à¸à¸²à¸/à¸à¸²à¸à¹€à¸‡à¸´à¸™ (à¸¥à¸´à¸‡à¸à¹Œ DEPOSIT_URL)

    à¹à¸à¹‰à¸›à¸±à¸à¸«à¸² NameError: flex_backoffice_button à¹„à¸¡à¹ˆà¸–à¸¹à¸à¸›à¸£à¸°à¸à¸²à¸¨
    """
    u = (url or '').strip() or DEPOSIT_URL
    # à¸à¸±à¸™à¸žà¸´à¸¡à¸žà¹Œà¸¥à¸´à¸‡à¸à¹Œà¹à¸šà¸šà¹„à¸¡à¹ˆà¸¡à¸µ scheme
    if not re.match(r'^https?://', u, re.IGNORECASE):
        u = 'https://' + u.lstrip('/')

    return FlexSendMessage(
        alt_text='à¸à¸²à¸à¹€à¸‡à¸´à¸™/à¹à¸ˆà¹‰à¸‡à¹‚à¸­à¸™',
        contents={
            'type': 'bubble',
            'size': 'mega',
            'styles': {'body': {'backgroundColor': '#F3F4F6'}},
            'body': {
                'type': 'box',
                'layout': 'vertical',
                'paddingAll': '12px',
                'contents': [
                    {
                        'type': 'box',
                        'layout': 'vertical',
                        'backgroundColor': '#FFFFFF',
                        'cornerRadius': '16px',
                        'paddingAll': '16px',
                        'spacing': '10px',
                        'contents': [
                            {
                                'type': 'text',
                                'text': 'ðŸ’³ à¸à¸²à¸à¹€à¸‡à¸´à¸™ / à¹à¸ˆà¹‰à¸‡à¹‚à¸­à¸™',
                                'weight': 'bold',
                                'size': 'lg',
                                'align': 'center',
                                'color': '#111827'
                            },
                            {
                                'type': 'text',
                                'text': 'à¸à¸”à¸›à¸¸à¹ˆà¸¡à¸”à¹‰à¸²à¸™à¸¥à¹ˆà¸²à¸‡à¹€à¸žà¸·à¹ˆà¸­à¹„à¸›à¸«à¸™à¹‰à¸²à¹à¸ˆà¹‰à¸‡à¸à¸²à¸/à¹à¸™à¸šà¸ªà¸¥à¸´à¸›',
                                'size': 'sm',
                                'align': 'center',
                                'wrap': True,
                                'color': '#6B7280'
                            },
                            {'type': 'separator', 'margin': 'md', 'color': '#E5E7EB'},
                            {
                                'type': 'button',
                                'style': 'primary',
                                'color': '#16A34A',
                                'height': 'sm',
                                'action': {'type': 'uri', 'label': label, 'uri': u}
                            }
                        ]
                    }
                ]
            }
        }
    )



def flex_result_preview(code: str, pair_no: int):
    # ---- mapping à¸ªà¸µ/à¹„à¸­à¸„à¸­à¸™/à¸„à¸³à¸­à¸˜à¸´à¸šà¸²à¸¢ à¸•à¸²à¸¡à¸œà¸¥ ----
    meta = {
        "à¸ª": {"title": "à¸ªà¸¹à¸‡à¸Šà¸™à¸°", "accent": "#00C853", "icon": "âœ…", "desc": f"à¸ˆà¹ˆà¸²à¸¢ 1 : {PROFIT_RATE:.2f}"},
        "à¸•": {"title": "à¸•à¹ˆà¸³à¸Šà¸™à¸°", "accent": "#A51212CA", "icon": "âŒ", "desc": f"à¸ˆà¹ˆà¸²à¸¢ 1 : {PROFIT_RATE:.2f}"},
        "à¸": {"title": f"à¸à¸¥à¸²à¸‡ (à¸„à¸·à¸™à¹€à¸‡à¸´à¸™ à¸«à¸±à¸ {int(MIDDLE_FEE*100)}%)", "accent": "#F59E0B", "icon": "ðŸŸ¡", "desc": "à¸„à¸·à¸™à¹€à¸‡à¸´à¸™à¹à¸šà¸šà¸«à¸±à¸à¸„à¹ˆà¸²à¸˜à¸£à¸£à¸¡à¹€à¸™à¸µà¸¢à¸¡"},
        "à¸ˆ": {"title": "à¸ˆà¸²à¸§ (à¸„à¸·à¸™à¹€à¸•à¹‡à¸¡)", "accent": "#22C55E", "icon": "ðŸŸ¢", "desc": "à¸„à¸·à¸™à¹€à¸‡à¸´à¸™à¹€à¸•à¹‡à¸¡à¸ˆà¸³à¸™à¸§à¸™"},
        "à¸¡": {"title": "à¹€à¸ªà¸¡à¸­-à¸«à¸²à¸¢ (à¸„à¸·à¸™à¹€à¸•à¹‡à¸¡)", "accent": "#22C55E", "icon": "ðŸŸ¢", "desc": "à¸„à¸·à¸™à¹€à¸‡à¸´à¸™à¹€à¸•à¹‡à¸¡à¸ˆà¸³à¸™à¸§à¸™"},
        "à¸•à¸ˆ": {"title": f"à¸•à¹ˆà¸³à¹€à¸ªà¸¡à¸­ (à¸«à¸±à¸ {int(MIDDLE_FEE*100)}%) / à¸ªà¸¹à¸‡à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡", "accent": "#A855F7", "icon": "ðŸŸ£", "desc": "à¸•à¸²à¸¡à¸™à¹‚à¸¢à¸šà¸²à¸¢à¸žà¸´à¹€à¸¨à¸©"},
        "à¸•à¸ª": {"title": f"à¸•à¹ˆà¸³à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡ / à¸ªà¸¹à¸‡à¹€à¸ªà¸¡à¸­ (à¸«à¸±à¸ {int(MIDDLE_FEE*100)}%)", "accent": "#A855F7", "icon": "ðŸŸ£", "desc": "à¸•à¸²à¸¡à¸™à¹‚à¸¢à¸šà¸²à¸¢à¸žà¸´à¹€à¸¨à¸©"},
    }
    m = meta.get(code, {"title": "à¹ƒà¸ªà¹ˆà¸œà¸¥à¸œà¸´à¸”à¹ƒà¸ªà¹ˆà¹ƒà¸«à¸¡à¹ˆ", "accent": "#94A3B8", "icon": "âšª", "desc": "à¸•à¸£à¸§à¸ˆà¸ªà¸­à¸šà¸£à¸«à¸±à¸ªà¸œà¸¥à¸­à¸µà¸à¸„à¸£à¸±à¹‰à¸‡"})
    title = m["title"]
    accent = m["accent"]
    icon = m["icon"]
    desc = m["desc"]

    # à¸ªà¸µà¸•à¸±à¸§à¸­à¸±à¸à¸©à¸£à¸œà¸¥: à¹‚à¸—à¸™à¹€à¸‚à¸µà¸¢à¸§à¸ªà¸³à¸«à¸£à¸±à¸šà¸„à¸·à¸™à¹€à¸•à¹‡à¸¡/à¸ˆà¸²à¸§/à¸¡, à¹‚à¸—à¸™à¸›à¸à¸•à¸´à¸à¸£à¸“à¸µà¸­à¸·à¹ˆà¸™
    text_color = "#10B981" if any(k in code for k in ("à¸ˆ", "à¸¡")) else "#E5E7EB"

    return FlexSendMessage(
        alt_text=f"à¸ªà¸£à¸¸à¸›à¸œà¸¥: {title}",
        contents={
            "type": "bubble",
            "size": "mega",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "0px",
                "contents": [
                    # ---- Header (à¹à¸–à¸šà¸ªà¸µ) ----
                    {
                        "type": "box",
                        "layout": "vertical",
                        "paddingAll": "14px",
                        "backgroundColor": accent,
                        "contents": [
                            {
                                "type": "text",
                                "text": f"{icon} à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸£à¸­à¸šà¸—à¸µà¹ˆ {pair_no}",
                                "weight": "bold",
                                "size": "lg",
                                "align": "center",
                                "color": "#0B1220"
                            }
                        ]
                    },
                    # ---- Card ----
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#0F172A",
                        "paddingAll": "16px",
                        "spacing": "12px",
                        "contents": [
                            # Title row
                            {
                                "type": "box",
                                "layout": "horizontal",
                                "contents": [
                                    {
                                        "type": "box",
                                        "layout": "vertical",
                                        "width": "6px",
                                        "backgroundColor": accent,
                                        "cornerRadius": "6px",
                                        "height": "52px"
                                    },
                                    {
                                        "type": "box",
                                        "layout": "vertical",
                                        "paddingAll": "10px",
                                        "contents": [
                                            {
                                                "type": "text",
                                                "text": title,
                                                "weight": "bold",
                                                "size": "xl",
                                                "wrap": True,
                                                "color": text_color,
                                                "align": "start"
                                            },
                                            {
                                                "type": "text",
                                                "text": desc,
                                                "size": "xs",
                                                "color": "#94A3B8",
                                                "wrap": True
                                            }
                                        ]
                                    }
                                ],
                                "spacing": "10px",
                                "cornerRadius": "10px"
                            },

                            {"type": "separator", "color": "#334155"},

                            # Quick tips
                            {
                                "type": "box",
                                "layout": "vertical",
                                "spacing": "6px",
                                "contents": [
                                    {
                                        "type": "text",
                                        "text": "à¸‚à¸±à¹‰à¸™à¸•à¸­à¸™à¸–à¸±à¸”à¹„à¸›",
                                        "size": "sm",
                                        "weight": "bold",
                                        "color": "#CBD5E1"
                                    },
                                    {
                                        "type": "box",
                                        "layout": "vertical",
                                        "backgroundColor": "#111827",
                                        "cornerRadius": "8px",
                                        "paddingAll": "10px",
                                        "contents": [
                                            {
                                                "type": "text",
                                                "text": "à¸žà¸´à¸¡à¸žà¹Œ  à¹€à¸žà¸·à¹ˆà¸­à¸¢à¸·à¸™à¸¢à¸±à¸™à¸œà¸¥",
                                                "size": "sm",
                                                "color": "#E5E7EB",
                                                "wrap": True
                                            },
                                            {
                                                "type": "text",
                                                "text": "à¸«à¸²à¸à¸•à¹‰à¸­à¸‡à¸à¸²à¸£à¹€à¸›à¸¥à¸µà¹ˆà¸¢à¸™à¸œà¸¥: à¸žà¸´à¸¡à¸žà¹Œ s<à¹‚à¸„à¹‰à¸”à¸œà¸¥> à¸­à¸µà¸à¸„à¸£à¸±à¹‰à¸‡",
                                                "size": "xs",
                                                "color": "#94A3B8",
                                                "wrap": True
                                            }
                                        ]
                                    }
                                ]
                            }
                        ]
                    }
                ]
            }
        }
    )


def flex_settle(pair_no, rows, footer_text,
                show_profit=False, profit_value=0,
                balance_map=None,
                accum=None,
                camp_name=None):  # <--- à¸£à¸±à¸šà¸•à¸±à¸§à¹à¸›à¸£ camp_name à¹€à¸žà¸´à¹ˆà¸¡
    
    def _fmt_signed(n: int) -> str:
        return f"+{fmt(n)}" if n >= 0 else f"-{fmt(abs(n))}"

    has_balance = bool(balance_map)
    has_accum   = bool(accum)

    # --- 1. à¸ªà¹ˆà¸§à¸™à¸«à¸±à¸§à¸‚à¹‰à¸­ (Header) à¸›à¸£à¸±à¸šà¹ƒà¸«à¸¡à¹ˆà¹ƒà¸«à¹‰à¹‚à¸Šà¸§à¹Œ à¸£à¸­à¸š à¹à¸¥à¸° à¸„à¹ˆà¸²à¸¢ ---
    header_contents = [
        # à¸šà¸£à¸£à¸—à¸±à¸”à¸—à¸µà¹ˆ 1: à¸£à¸­à¸šà¸—à¸µà¹ˆ (à¸•à¸±à¸§à¹ƒà¸«à¸à¹ˆ à¸ªà¸µà¸—à¸­à¸‡)
        {
            "type": "text",
            "text": f"à¸£à¸­à¸šà¸—à¸µà¹ˆ {pair_no}",
            "weight": "bold",
            "align": "center",
            "size": "xxl",
            "color": "#FDE68A"  # à¸ªà¸µà¸—à¸­à¸‡
        }
    ]
    
    # à¸šà¸£à¸£à¸—à¸±à¸”à¸—à¸µà¹ˆ 2: à¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢ (à¸–à¹‰à¸²à¸¡à¸µ)
    if camp_name:
        header_contents.append({
            "type": "text",
            "text": f"ðŸš€ à¸„à¹ˆà¸²à¸¢: {camp_name}",
            "weight": "bold",
            "align": "center",
            "size": "md",
            "color": "#FFFFFF",
            "margin": "sm"
        })
    else:
        # à¸–à¹‰à¸²à¹„à¸¡à¹ˆà¸¡à¸µà¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢ à¹ƒà¸«à¹‰à¸‚à¸¶à¹‰à¸™à¸§à¹ˆà¸² à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸à¸²à¸£à¹à¸—à¸‡ à¹à¸—à¸™
        header_contents.insert(0, {
             "type": "text", "text": "ðŸ“Š à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸à¸²à¸£à¹à¸—à¸‡", 
             "weight": "bold", "align": "center", "size": "md", "color": "#FFFFFF"
        })

    # --- 2. à¸ªà¹ˆà¸§à¸™à¸£à¸²à¸¢à¸à¸²à¸£à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™ (Body) ---
    header_cols = [
        {"type": "text", "text": "à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™",  "flex": 4, "size": "md", "weight": "bold", "color": "#FFFFFF"},
        {"type": "text", "text": "à¸¢à¸­à¸”à¹€à¸¥à¹ˆà¸™", "flex": 3, "size": "md", "align": "end", "weight": "bold", "color": "#FFFFFF"},
        {"type": "text", "text": "à¹„à¸”à¹‰à¹€à¸ªà¸µà¸¢",  "flex": 3, "size": "md", "align": "end", "weight": "bold", "color": "#FFFFFF"},
    ]
    if has_balance:
        header_cols.append({"type": "text", "text": "à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­", "flex": 3, "size": "md", "align": "end", "weight": "bold", "color": "#FFFFFF"})

    lines = []
    if rows:
        lines.append({"type": "box", "layout": "horizontal", "contents": header_cols})
        lines.append({"type": "separator", "margin": "sm", "color": "#4B5563"})
        for r in rows:
            pl = (r.get("payout", 0) or 0) - (r.get("stake", 0) or 0)
            pl_color = "#10B981" if pl > 0 else ("#EF4444" if pl < 0 else "#E5E7EB")

            row_cols = [
                {"type": "text", "text": r["name"],       "flex": 4, "size": "md", "color": "#E5E7EB"},
                {"type": "text", "text": fmt(r["stake"]), "flex": 3, "size": "md", "align": "end", "color": "#F9FAFB"},
                {"type": "text", "text": _fmt_signed(pl), "flex": 3, "size": "md", "align": "end", "color": pl_color},
            ]
            if has_balance:
                bal = balance_map.get(r["uid"], 0)
                row_cols.append({"type": "text", "text": fmt(bal), "flex": 3, "size": "md", "align": "end", "color": "#FACC15"})
            lines.append({"type": "box", "layout": "horizontal", "contents": row_cols})
    else:
        lines.append({"type": "text", "text": "(à¹„à¸¡à¹ˆà¸¡à¸µà¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™)", "size": "md", "align": "center", "color": "#9CA3AF"})

    # --- 3. à¸ªà¹ˆà¸§à¸™à¸ªà¸£à¸¸à¸›à¸à¸³à¹„à¸£ (Footer) ---
    if show_profit:
        lines.append({"type": "separator", "margin": "md", "color": "#4B5563"})
        lines.append({"type": "text", "text": f"ðŸ’° à¸à¸³à¹„à¸£à¸£à¸­à¸šà¸™à¸µà¹‰: {_fmt_signed(profit_value)}",
                      "align": "end", "weight": "bold", "size": "md", "color": "#FACC15"})
        if has_accum:
            lines.append({"type": "text",
                          "text": f"ðŸ“ˆ à¸ªà¸°à¸ªà¸¡à¸à¸³à¹„à¸£: {fmt(accum['profit_sum'])} â€¢ à¸‚à¸²à¸”à¸—à¸¸à¸™: {fmt(accum['loss_sum'])}",
                          "align": "end", "size": "sm", "color": "#E5E7EB"})
            lines.append({"type": "text",
                          "text": f"ðŸ§® à¸ªà¸¸à¸—à¸˜à¸´à¸ªà¸°à¸ªà¸¡: {_fmt_signed(accum['net'])}",
                          "align": "end", "weight": "bold", "size": "md",
                          "color": "#10B981" if accum["net"] >= 0 else "#EF4444"})

    return FlexSendMessage(
        alt_text=f"à¸ªà¸£à¸¸à¸›à¸œà¸¥ à¸£à¸­à¸š {pair_no}",
        contents={
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "0px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#16A34A",
                        "paddingAll": "14px",
                        "contents": header_contents # à¹ƒà¸Šà¹‰à¸ªà¹ˆà¸§à¸™à¸«à¸±à¸§à¸—à¸µà¹ˆà¸ªà¸£à¹‰à¸²à¸‡à¹„à¸§à¹‰à¸”à¹‰à¸²à¸™à¸šà¸™
                    },
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#1F2937",
                        "paddingAll": "18px",
                        "spacing": "md",
                        "contents": lines + [
                            {"type": "separator", "margin": "md", "color": "#4B5563"},
                            {"type": "text", "text": footer_text, "align": "end", "size": "md", "color": "#9CA3AF"}
                        ]
                    }
                ]
            }
        }
    )

def flex_scoreboard(history_list):
    # Mapping à¸œà¸¥: à¹€à¸›à¸¥à¸µà¹ˆà¸¢à¸™à¸ˆà¸²à¸à¸ªà¸µà¸žà¸·à¹‰à¸™à¸«à¸¥à¸±à¸‡ à¹€à¸›à¹‡à¸™à¸ªà¸µà¸•à¸±à¸§à¸­à¸±à¸à¸©à¸£ (color)
    res_map = {
        "à¸ª":  {"text": "à¸ªà¸¹à¸‡ âœ…", "color": "#22C55E"},
        "à¸•":  {"text": "à¸•à¹ˆà¸³ âŒ", "color": "#EF4444"},
        "à¸":  {"text": "à¸à¸¥à¸²à¸‡ â›”", "color": "#EAB308"},
        "à¸ˆ":  {"text": "à¸ˆà¸²à¸§ â›”", "color": "#3B82F6"},
        "à¸¡":  {"text": "à¹€à¸ªà¸¡à¸­ â›”", "color": "#3B82F6"},
        "à¸•à¸ˆ": {"text": "à¸•à¹ˆà¸³à¹€à¸ªà¸¡à¸­ à¸ªà¸¹à¸‡à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡ â›”âŒ", "color": "#A855F7"},
        "à¸•à¸ª": {"text": "à¸•à¹ˆà¸³à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡ à¸ªà¸¹à¸‡à¹€à¸ªà¸¡à¸­ âœ…â›”", "color": "#A855F7"},
    }

    # ===== ðŸ”¥ à¸ˆà¸¸à¸”à¹à¸à¹‰à¸ˆà¸£à¸´à¸‡: à¸„à¸±à¸”à¹€à¸«à¸¥à¸·à¸­à¸œà¸¥à¸¥à¹ˆà¸²à¸ªà¸¸à¸”à¸•à¹ˆà¸­à¸£à¸­à¸š =====
    latest_by_round = {}
    for h in history_list or []:
        r = h.get("round")
        if r is None:
            continue
        latest_by_round[r] = h   # à¸•à¸±à¸§à¸«à¸¥à¸±à¸‡à¸—à¸±à¸šà¸•à¸±à¸§à¸à¹ˆà¸­à¸™ (à¸œà¸¥à¸¥à¹ˆà¸²à¸ªà¸¸à¸”)

    # à¹€à¸£à¸µà¸¢à¸‡à¸•à¸²à¸¡à¸£à¸­à¸š à¹à¸¥à¹‰à¸§à¹€à¸­à¸² 10 à¸£à¸­à¸šà¸¥à¹ˆà¸²à¸ªà¸¸à¸”
    recent = [latest_by_round[r] for r in sorted(latest_by_round)][-10:]

    rows = []

    # --- à¸ªà¹ˆà¸§à¸™à¸«à¸±à¸§à¸•à¸²à¸£à¸²à¸‡ ---
    rows.append({
        "type": "box",
        "layout": "horizontal",
        "paddingBottom": "10px",
        "contents": [
            {"type": "text", "text": "#", "flex": 1, "size": "xs", "color": "#6B7280", "align": "center"},
            {"type": "text", "text": "à¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢ ", "flex": 3, "size": "xs", "color": "#6B7280", "offsetStart": "10px"},
            {"type": "text", "text": "à¸œà¸¥ ", "flex": 4, "size": "xs", "align": "center", "color": "#6B7280"},
        ]
    })

    # à¸§à¸™à¸¥à¸¹à¸›à¸ªà¸£à¹‰à¸²à¸‡à¹à¸–à¸§à¸‚à¹‰à¸­à¸¡à¸¹à¸¥
    for idx, item in enumerate(recent):
        code_key = item.get('code', '?')

        if code_key in res_map:
            style = res_map[code_key]
        else:
            base_code = code_key[0] if code_key else "?"
            style = res_map.get(base_code, {"text": code_key, "color": "#FFFFFF"})

        camp_name = item.get('camp') or "-"

        rows.append({
            "type": "box",
            "layout": "horizontal",
            "paddingVertical": "8px",
            "alignItems": "center",
            "contents": [
                {
                    "type": "text",
                    "text": str(item['round']),
                    "flex": 1,
                    "size": "xs",
                    "color": "#9CA3AF",
                    "align": "center"
                },
                {
                    "type": "text",
                    "text": camp_name,
                    "flex": 3,
                    "size": "sm",
                    "color": "#E5E7EB",
                    "wrap": False,
                    "offsetStart": "10px"
                },
                {
                    "type": "text",
                    "text": style['text'],
                    "flex": 4,
                    "color": style['color'],
                    "weight": "bold",
                    "align": "center",
                    "size": "xxs" if len(style['text']) > 8 else "xs",
                    "wrap": True
                }
            ]
        })

        if idx < len(recent) - 1:
            rows.append({"type": "separator", "color": "#1F2937", "margin": "none"})

    return FlexSendMessage(
        alt_text="à¸ªà¸à¸­à¸šà¸±à¹‰à¸‡à¹„à¸Ÿà¸¥à¹ˆà¸²à¸ªà¸¸à¸”",
        contents={
            "type": "bubble",
            "size": "mega",
            "styles": {
                "header": {"backgroundColor": "#111827"},
                "body": {"backgroundColor": "#111827"}
            },
            "header": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "20px",
                "contents": [
                    {
                        "type": "text",
                        "text": "ðŸ“œ à¸ªà¸à¸­à¸šà¸±à¹‰à¸‡à¹„à¸Ÿ",
                        "weight": "bold",
                        "size": "lg",
                        "color": "#FBBF24",
                        "align": "center"
                    }
                ]
            },
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingTop": "0px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#1F2937",
                        "cornerRadius": "10px",
                        "paddingAll": "12px",
                        "contents": rows if rows else [
                            {
                                "type": "text",
                                "text": "(à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸›à¸£à¸°à¸§à¸±à¸•à¸´)",
                                "align": "center",
                                "color": "#6B7280",
                                "size": "sm",
                                "paddingAll": "20px"
                            }
                        ]
                    }
                ]
            }
        }
    )


def flex_call_pages(user_rows, title="à¸•à¸²à¸£à¸²à¸‡à¹€à¸„à¸£à¸”à¸´à¸•à¸¥à¸¹à¸à¸„à¹‰à¸²", per_page=30):
    pages = []
    total = len(user_rows)
    num_pages = max(1, ceil(total / per_page))
    sum_credit_all = sum(int(r.get("credit", 0) or 0) for r in user_rows)

    def fmt2(n):
        try:
            return f"{int(float(n or 0)):,}"
        except:
            return "0"

    updated_at = datetime.now().strftime("%d/%m/%Y %H:%M")

    # ========== HEAD TABLE: à¸‚à¸™à¸²à¸”à¹€à¸¥à¹‡à¸à¸¥à¸‡ 100% à¸—à¸³à¸‡à¸²à¸™à¹„à¸”à¹‰ ==========
    def table_head():
        return {
            "type": "box",
            "layout": "horizontal",
            "paddingAll": "6px",
            "backgroundColor": "#E6F0FF",
            "contents": [
                {"type": "text", "text": "ID", "flex": 3, "size": "xs", "weight": "bold", "color": "#1E3A8A"},
                {"type": "text", "text": "à¸Šà¸·à¹ˆà¸­", "flex": 6, "size": "xs", "weight": "bold", "color": "#1E3A8A"},
                {"type": "text", "text": "à¹€à¸„à¸£à¸”à¸´à¸•", "flex": 3, "size": "xs", "weight": "bold", "align": "end", "color": "#1E3A8A"},
            ]
        }

    for i in range(num_pages):
        chunk = user_rows[i * per_page:(i + 1) * per_page]
        page_credit = sum(int(r.get("credit", 0) or 0) for r in chunk)

        header = {
            "type": "box",
            "layout": "vertical",
            "paddingAll": "6px",
            "contents": [
                {"type": "text", "text": title, "weight": "bold", "size": "sm", "align": "center"},
                {"type": "text", "text": f"à¸«à¸™à¹‰à¸² {i+1}/{num_pages} â€¢ à¸­à¸±à¸›à¹€à¸”à¸• {updated_at}", "size": "xs", "align": "center", "color": "#6B7280"}
            ]
        }

        rows = []
        rows.append(table_head())
        rows.append({"type": "separator", "margin": "md", "color": "#D1D5DB"})

        # ========== ROWS ==========
        if chunk:
            for idx, r in enumerate(chunk):
                cid = str(r.get("cid", "-"))
                name = str(r.get("name", "-"))
                cred = int(r.get("credit", 0) or 0)

                row_bg = "#FFFFFF"

                rows.append({
                    "type": "box",
                    "layout": "horizontal",
                    "paddingAll": "4px",   # à¸¥à¸” padding à¹à¸•à¹ˆà¹„à¸¡à¹ˆà¸–à¸¶à¸‡à¸‚à¸±à¹‰à¸™à¸žà¸±à¸‡
                    "backgroundColor": row_bg,
                    "contents": [
                        {"type": "text", "text": cid, "flex": 3, "size": "xs", "color": "#111827"},
                        {"type": "text", "text": name, "flex": 6, "size": "xs", "wrap": True, "color": "#111827"},
                        {"type": "text", "text": fmt2(cred), "flex": 3, "size": "xs", "align": "end", "color": "#111827"},
                    ]
                })

                if idx != len(chunk) - 1:
                    rows.append({"type": "separator", "margin": "md", "color": "#E5E7EB"})
        else:
            rows.append({
                "type": "box",
                "layout": "vertical",
                "paddingAll": "8px",
                "contents": [{"type": "text", "text": "(à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸‚à¹‰à¸­à¸¡à¸¹à¸¥)", "align": "center", "size": "xs", "color": "#9CA3AF"}]
            })

        # ========== SUMMARY ==========
        summary = {
            "type": "box",
            "layout": "vertical",
            "spacing": "4px",
            "paddingAll": "6px",
            "contents": [
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "à¸¥à¸¹à¸à¸„à¹‰à¸²à¹ƒà¸™à¸«à¸™à¹‰à¸²à¸™à¸µà¹‰", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": str(len(chunk)), "flex": 6, "size": "xs", "align": "end"},
                ]},
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "à¸£à¸§à¸¡à¹€à¸„à¸£à¸”à¸´à¸• (à¸«à¸™à¹‰à¸²à¸™à¸µà¹‰)", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": fmt2(page_credit), "flex": 6, "size": "xs", "align": "end", "color": "#16A34A"},
                ]},
                {"type": "separator", "margin": "md"},
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "à¸£à¸§à¸¡à¹€à¸„à¸£à¸”à¸´à¸• (à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”)", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": fmt2(sum_credit_all), "flex": 6, "size": "xs", "align": "end", "color": "#16A34A"},
                ]}
            ]
        }

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "4px",
                "paddingAll": "8px",
                "contents": [
                    header,
                    {"type": "box", "layout": "vertical", "contents": rows},
                    summary
                ]
            }
        }

        pages.append(FlexSendMessage(
            alt_text=f"{title} {i+1}/{num_pages}",
            contents=bubble
        ))

    return pages




@lru_cache(maxsize=None)
def rules_text() -> str:
    return (
        "ðŸŽ‰ðŸŽŠà¸à¸•à¸´à¸à¸²ðŸŽŠðŸŽ‰\n"
        f"âœ¨à¹à¸—à¸‡à¸‚à¸±à¹‰à¸™à¸•à¹ˆà¸³{MIN_BET}-{fmt(MAX_BET)}à¸šà¸²à¸—/à¸„à¸™/à¸£à¸­à¸š\n"
        "\n"
        "ðŸ†à¸à¸²à¸£à¸ˆà¹ˆà¸²à¸¢ðŸŽ–ï¸\n"
        f"à¸Šà¸™à¸° à¸ˆà¹ˆà¸²à¸¢ 1 : {PROFIT_RATE:.2f}\n"
        "\n"
        f"ðŸ”´à¸­à¸±à¹‰à¸™à¸•à¹ˆà¸³ = {fmt(SIDE_CAP['LO'])}\n"
        f"ðŸ”µà¸­à¸±à¹‰à¸™à¸ªà¸¹à¸‡ = {fmt(SIDE_CAP['HI'])}\n"
        f"ðŸŸ¢à¸­à¸­à¸à¸à¸¥à¸²à¸‡à¹€à¸ˆà¹Šà¸² à¸«à¸±à¸ {int(MIDDLE_FEE*100)}%\n"
        "\n"
        "- à¸ˆà¸³à¸à¸±à¸” 1 à¸šà¸´à¸¥/à¸£à¸­à¸š à¹à¸¥à¸°à¸«à¹‰à¸²à¸¡à¹à¸—à¸‡à¸ªà¸§à¸™ (à¸•à¹‰à¸­à¸‡à¸¢à¸à¹€à¸¥à¸´à¸à¸šà¸´à¸¥à¹€à¸”à¸´à¸¡à¸à¹ˆà¸­à¸™)\n"
        "- à¸žà¸´à¸¡à¸žà¹Œ x à¹€à¸žà¸·à¹ˆà¸­à¸¢à¸à¹€à¸¥à¸´à¸à¸šà¸´à¸¥ / à¸žà¸´à¸¡à¸žà¹Œ C à¹€à¸žà¸·à¹ˆà¸­à¸”à¸¹à¸šà¸±à¸•à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸\n"
    )


# ====== RESULT CALC (à¸•à¸²à¸¡à¹‚à¸¡à¹€à¸”à¸¥ escrow) ======
def settle_by_code(st, code):
    """
    à¹‚à¸¡à¹€à¸”à¸¥à¹€à¸„à¸£à¸”à¸´à¸•:
    - à¸•à¸­à¸™à¸£à¸±à¸šà¸šà¸´à¸¥: à¸«à¸±à¸à¹€à¸„à¸£à¸”à¸´à¸• = amount à¹à¸¥à¸°à¹€à¸à¹‡à¸š st['escrow'][uid] += amount
    - à¸•à¸­à¸™à¸ªà¸£à¸¸à¸›:
        * à¸Šà¸™à¸°: à¸„à¸·à¸™à¸•à¹‰à¸™à¸—à¸¸à¸™ + à¸à¸³à¹„à¸£à¸ªà¸¸à¸—à¸˜à¸´ (amount + amount*PROFIT_RATE)
        * à¹à¸žà¹‰: à¹„à¸¡à¹ˆà¸„à¸·à¸™à¸­à¸°à¹„à¸£ (à¸•à¹‰à¸™à¸—à¸¸à¸™à¸–à¸¹à¸à¸«à¸±à¸à¹„à¸›à¹à¸¥à¹‰à¸§)
        * à¸„à¸·à¸™à¹€à¸‡à¸´à¸™à¸«à¸±à¸ fee: à¸„à¸·à¸™ amount*(1 - fee)
        * à¸„à¸·à¸™à¹€à¸•à¹‡à¸¡: à¸„à¸·à¸™ amount
    à¸Ÿà¸±à¸‡à¸à¹Œà¸Šà¸±à¸™à¸™à¸µà¹‰à¸„à¸·à¸™ rows: [{'uid','name','stake','payout'}...], footer_text
    """
    acc = {}
    def add(uid, name, stake, payout):
        row = acc.get(uid, {"uid": uid, "name": name, "stake": 0, "payout": 0})
        row["stake"] += stake
        row["payout"] += payout
        acc[uid] = row

    d = RESULT_DEFS.get(code)

    # DRAW (à¸„à¸·à¸™à¹€à¸•à¹‡à¸¡)
    if (not d) or d.get("special") == "DRAW_0":
        for b in st["bet_index"].values():
            add(b["uid"], b["name"], b["amount"], b["amount"])
        label = RESULT_DEFS.get(code, {"label": "à¸ˆà¸²à¸§ (à¸„à¸·à¸™à¹€à¸•à¹‡à¸¡)"} )["label"]
        return list(acc.values()), f"à¸œà¸¥: {label}"

    # à¸à¸¥à¸²à¸‡à¸„à¸·à¸™à¹€à¸‡à¸´à¸™ à¸«à¸±à¸ MIDDLE_FEE
    if d.get("special") == "MIDDLE_FEE":
        for b in st["bet_index"].values():
            refund = _round_refund(b["amount"] * (1 - MIDDLE_FEE))
            add(b["uid"], b["name"], b["amount"], refund)
        return list(acc.values()), f"à¸œà¸¥: à¸à¸¥à¸²à¸‡ (à¸„à¸·à¸™à¹€à¸‡à¸´à¸™ à¸«à¸±à¸ {int(MIDDLE_FEE*100)}%)"

    # à¸•à¹ˆà¸³à¹€à¸ªà¸¡à¸­ (à¸«à¸±à¸ fee) / à¸ªà¸¹à¸‡à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡
    if d.get("special") == "LOW_DRAWFEE_HIGH_LOSE":
        for b in st["bet_index"].values():
            if b["side"] == "LO":
                refund = _round_refund(b["amount"] * (1 - MIDDLE_FEE))
                add(b["uid"], b["name"], b["amount"], refund)
            else:
                add(b["uid"], b["name"], b["amount"], 0)
        return list(acc.values()), f"à¸œà¸¥: à¸•à¹ˆà¸³à¹€à¸ªà¸¡à¸­ (à¸«à¸±à¸ {int(MIDDLE_FEE*100)}%) / à¸ªà¸¹à¸‡à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡"

    # à¸•à¹ˆà¸³à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡ / à¸ªà¸¹à¸‡à¹€à¸ªà¸¡à¸­ (à¸«à¸±à¸ fee)
    if d.get("special") == "LOW_LOSE_HIGH_DRAWFEE":
        for b in st["bet_index"].values():
            if b["side"] == "HI":
                refund = round(b["amount"] * (1 - MIDDLE_FEE))
                add(b["uid"], b["name"], b["amount"], refund)
            else:
                add(b["uid"], b["name"], b["amount"], 0)
        return list(acc.values()), f"à¸œà¸¥: à¸•à¹ˆà¸³à¹€à¸ªà¸µà¸¢à¹€à¸•à¹‡à¸¡ / à¸ªà¸¹à¸‡à¹€à¸ªà¸¡à¸­ (à¸«à¸±à¸ {int(MIDDLE_FEE*100)}%)"

    # à¸›à¸à¸•à¸´: à¸¡à¸µà¸à¸±à¹ˆà¸‡à¸Šà¸™à¸°/à¹à¸žà¹‰
    win = d["winner"]
    for b in st["bet_index"].values():
        if b["side"] == win:
            payout = b["amount"] + _round_profit(b["amount"] * PROFIT_RATE)
            add(b["uid"], b["name"], b["amount"], payout)
        else:
            add(b["uid"], b["name"], b["amount"], 0)
    return list(acc.values()), f"à¸œà¸¥: {d['label']}"

# ========= HARDENING / SECURITY =========
MAX_BODY_BYTES = int(os.getenv("MAX_BODY_BYTES", "200000"))
WEBHOOK_DRIFT_SEC = int(os.getenv("WEBHOOK_DRIFT_SEC", "600"))  # DEV-friendly
REQUIRE_LINE_UA = os.getenv("REQUIRE_LINE_UA", "0") == "1"




RL_IP_LIMIT, RL_IP_PERIOD = int(os.getenv("RL_IP_LIMIT", "150")), int(os.getenv("RL_IP_PERIOD", "60"))
RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD = int(os.getenv("RL_UID_BURST_LIMIT", "20")), int(os.getenv("RL_UID_BURST_PERIOD", "10"))
RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD = int(os.getenv("RL_ROOM_BURST_LIMIT", "220")), int(os.getenv("RL_ROOM_BURST_PERIOD", "10"))
RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD = int(os.getenv("RL_UID_DAILY_LIMIT", "3000")), 86400

MUTE_SECONDS_DEFAULT = int(os.getenv("MUTE_SECONDS_DEFAULT", "300"))
ABUSE_STRIKE_TO_MUTE  = int(os.getenv("ABUSE_STRIKE_TO_MUTE", "3"))

ALLOW_GROUP_IDS = {s.strip() for s in os.getenv("ALLOW_GROUP_IDS", "").split(",") if s.strip()}
DENY_GROUP_IDS  = {s.strip() for s in os.getenv("DENY_GROUP_IDS", "").split(",") if s.strip()}

ADMIN_PIN = os.getenv("ADMIN_PIN", "1234")

PROTECTED_UIDS = {s.strip() for s in os.getenv("PROTECTED_UIDS", "").split(",") if s.strip()}
LOCKDOWN_SECONDS_DEFAULT = int(os.getenv("LOCKDOWN_SECONDS_DEFAULT", "900"))  # 15m

class RateLimiter:
    def __init__(self): self._buckets = {}
    def allow(self, key: str, limit: int, period: int) -> bool:
        now = time.time()
        dq = self._buckets.get(key)
        if dq is None:
            dq = deque(); self._buckets[key] = dq
        while dq and (now - dq[0]) > period:
            dq.popleft()
        if len(dq) >= limit:
            return False
        dq.append(now)
        return True

rl = RateLimiter()
MUTED_UNTIL = {}       # uid -> ts
BANNED_UIDS = set()    # uid
BANNED_GROUPS = set()  # gid
STRIKES = {}           # uid -> count
_last_notice_at = {}   # uid -> ts
LOCKDOWN_UNTIL = {}    # gid -> ts

@lru_cache(maxsize=1024)
def _safe_is_line_ua(ua: str) -> bool:
    if not ua: return False
    ua = ua.lower()
    return ("linebotwebhook" in ua) or ("line-bot-sdk" in ua) or ("line" in ua and "webhook" in ua)

def _client_ip():
    xff = request.headers.get("X-Forwarded-For", "")
    if xff:
        return xff.split(",")[0].strip()
    return request.remote_addr or "0.0.0.0"

def _now(): return int(time.time())
def _muted(uid: str) -> bool: return MUTED_UNTIL.get(uid, 0) > _now()
def _locked_group(gid: str) -> bool: return LOCKDOWN_UNTIL.get(gid, 0) > _now()

def _notice_throttled(uid: str) -> bool:
    last = _last_notice_at.get(uid, 0)
    if _now() - last >= 30:
        _last_notice_at[uid] = _now()
        return False
    return True

def _admin_auth_pin(text: str) -> str:
    m = re.search(r"(?:\s|!!)(\d{4,8})\s*$", text)
    return m.group(1) if m else ""

def is_allowed_group(gid: str) -> bool:
    if gid in DENY_GROUP_IDS or gid in BANNED_GROUPS: return False
    if ALLOW_GROUP_IDS: return gid in ALLOW_GROUP_IDS or gid in BACKOFFICE_GROUP_IDS
    return True

def safe_reply(event, messages):
    """Reply message à¹à¸šà¸šà¹„à¸¡à¹ˆà¸—à¸³à¹ƒà¸«à¹‰à¸šà¸­à¸—à¸¥à¹ˆà¸¡ + retry à¹€à¸¡à¸·à¹ˆà¸­ timeout"""
    import requests as _requests
    for attempt in range(1, LINE_API_RETRY + 2):
        try:
            line_bot_api.reply_message(
                event.reply_token,
                messages,
                timeout=LINE_API_TIMEOUT
            )
            return True
        except (_requests.exceptions.Timeout, _requests.exceptions.ConnectionError) as e:
            if attempt <= LINE_API_RETRY:
                app.logger.warning("safe_reply timeout attempt=%d, retrying... (%s)", attempt, e)
                time.sleep(0.5 * attempt)
            else:
                app.logger.error("safe_reply timeout à¸«à¸¡à¸” retry (%d à¸„à¸£à¸±à¹‰à¸‡): %s", LINE_API_RETRY, e)
                return False
        except Exception:
            app.logger.exception("safe_reply failed")
            return False

def safe_push(to_id, messages, label: str = "", return_reason: bool = False):
    """Push message à¹à¸šà¸šà¹„à¸¡à¹ˆà¸—à¸³à¹ƒà¸«à¹‰à¸šà¸­à¸—à¸¥à¹ˆà¸¡ + retry à¹€à¸¡à¸·à¹ˆà¸­ timeout
    - à¸„à¸·à¸™à¸„à¹ˆà¸² True/False (à¸«à¸£à¸·à¸­ (True/False, reason) à¸–à¹‰à¸² return_reason=True)
    - reason: 'quota_exceeded' à¹€à¸¡à¸·à¹ˆà¸­à¹€à¸ˆà¸­ 429 monthly limit
    """
    import requests as _requests
    for attempt in range(1, LINE_API_RETRY + 2):
        try:
            line_bot_api.push_message(
                to_id,
                messages,
                timeout=LINE_API_TIMEOUT
            )
            return (True, None) if return_reason else True
        except (_requests.exceptions.Timeout, _requests.exceptions.ConnectionError) as e:
            if attempt <= LINE_API_RETRY:
                app.logger.warning("safe_push timeout attempt=%d, retrying to=%s (%s)", attempt, to_id, e)
                time.sleep(0.5 * attempt)
            else:
                app.logger.error("safe_push timeout à¸«à¸¡à¸” retry (%d à¸„à¸£à¸±à¹‰à¸‡) to=%s", LINE_API_RETRY, to_id)
                return (False, None) if return_reason else False
        except Exception as e:
            reason = None
            try:
                status = getattr(e, "status_code", None)
                err_resp = getattr(e, "error_response", None)
                msg = ""
                if isinstance(err_resp, dict):
                    msg = (err_resp.get("message") or "")
                else:
                    msg = str(e)

                if status == 429 and ("monthly limit" in msg.lower() or "reached your monthly limit" in msg.lower()):
                    reason = "quota_exceeded"
            except Exception:
                pass

            try:
                app.logger.exception(f"safe_push failed to={to_id} {label} reason={reason}".strip())
            except Exception:
                pass

            return (False, reason) if return_reason else False


def _member_name(gid, uid):
    try:
        p = line_bot_api.get_group_member_profile(gid, uid)
        return p.display_name
    except Exception:
        return uid

def _lockdown_and_alert(gid, uid):
    """à¸›à¹‰à¸­à¸‡à¸à¸±à¸™ kick à¸ªà¸³à¸„à¸±à¸: à¸¥à¹‡à¸­à¸à¸”à¸²à¸§à¸™à¹Œ + à¹à¸ˆà¹‰à¸‡à¹€à¸•à¸·à¸­à¸™ (no-op safety)."""
    LOCKDOWN_UNTIL[gid] = _now() + LOCKDOWN_SECONDS_DEFAULT
    try:
        name = _member_name(gid, uid)
        safe_push(gid, TextSendMessage(f"âš ï¸ à¸à¸¥à¸¸à¹ˆà¸¡à¸¥à¹‡à¸­à¸à¸”à¸²à¸§à¸™à¹Œà¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§ {LOCKDOWN_SECONDS_DEFAULT} à¸§à¸´à¸™à¸²à¸—à¸µ à¹€à¸žà¸£à¸²à¸°à¸ªà¸¡à¸²à¸Šà¸´à¸à¸ªà¸³à¸„à¸±à¸à¸­à¸­à¸: {name}"))
    except Exception:
        pass

# ====== ROUTES (secured webhook) ======
@app.route("/webhook", methods=["POST"])
@app.route("/callback", methods=["POST"])
def webhook():
    if request.content_length and request.content_length > MAX_BODY_BYTES:
        time.sleep(0.2)
        return "payload too large", 413

    if REQUIRE_LINE_UA:
        ua = request.headers.get("User-Agent", "")
        if not _safe_is_line_ua(ua):
            time.sleep(0.2)
            return "forbidden ua", 403

    ip = _client_ip()
    if not rl.allow(f"ip:{ip}", RL_IP_LIMIT, RL_IP_PERIOD):
        time.sleep(0.2)
        return "too many", 429

    body = request.get_data(as_text=True)
    ts_hdr = request.headers.get("X-Line-Request-Timestamp", "").strip()
    if ts_hdr.isdigit():
        try:
            tsv = int(ts_hdr)
            if tsv > 10**12: tsv = int(tsv / 1000)
            drift = abs(_now() - tsv)
            if drift > WEBHOOK_DRIFT_SEC:
                return "stale request", 401
        except Exception:
            pass

    sig = request.headers.get("X-Line-Signature", "")
    expected = base64.b64encode(hmac_new(CHANNEL_SECRET.encode(), body.encode(), sha256).digest()).decode()
    if not sig or not compare_digest(sig, expected):
        return "signature error", 400

    try:
        handler.handle(body, sig)
    except InvalidSignatureError:
        return "signature error", 400
    except Exception as e:
        app.logger.exception("err: %s", e)
        return "error", 500
    return "OK"

@app.get("/health")
def health(): return "OK", 200

@app.get("/copy/<acct>")
def copy_page(acct):
    acct = html_escape(acct.strip())
    logo_url = "https://image.tnews.co.th/uploads/images/contents/w1024/2025/01/CxaKtWLdkIgsdkMFfda3.webp?x-image-process=style/lg-webp"
    html = f"""<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>à¸„à¸±à¸”à¸¥à¸­à¸à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µ â€¢ à¸à¸ªà¸´à¸à¸£à¹„à¸—à¸¢</title>
<style>
  :root {{
    --bg:#0b1323; --card:#0f172a; --border:#334155; --text:#e5e7eb; --muted:#94a3b8;
    --brand:#16a34a; --brand-dark:#12803c; --warn:#f59e0b;
  }}
  html,body{{height:100%}}
  body{{margin:0;font-family:system-ui,-apple-system,"Segoe UI",Roboto,"Noto Sans Thai","Noto Sans",sans-serif;
       background:var(--bg);color:var(--text);display:flex;align-items:center;justify-content:center;padding:16px}}
  .card{{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:28px;max-width:520px;width:100%;
         box-shadow:0 10px 30px rgba(0,0,0,.35)}}
  .bank{{display:flex;align-items:center;gap:14px;margin-bottom:10px}}
  .bank-logo{{width:54px;height:54px;border-radius:50%;object-fit:cover;flex:0 0 54px;display:block}}
  .bank-title{{font-size:26px;font-weight:800;line-height:1.15}}
  .subtitle{{font-size:18px;color:var(--muted);margin-top:2px}}
  .acct-wrap{{margin:18px 0 8px;background:#091121;border:1px dashed var(--border);border-radius:14px;padding:18px;text-align:center}}
  .label{{font-size:18px;color:var(--muted);margin-bottom:6px}}
  .acct{{font-variant-numeric:tabular-nums;letter-spacing:.5px;font-size:34px;font-weight:800;color:#fde68a;word-break:break-word}}
  .help{{font-size:16px;color:var(--muted);margin:10px 0 18px}}
  .btns{{display:flex;gap:12px;flex-wrap:wrap}}
  button{{flex:1 1 180px;padding:16px 18px;border:0;border-radius:14px;cursor:pointer;font-size:20px;font-weight:800}}
  .primary{{background:var(--brand);color:#052e16}}
  .primary:hover{{background:var(--brand-dark)}}
  .secondary{{background:#0b1222;color:var(--text);border:1px solid var(--border)}}
  .status{{margin-top:16px;font-size:18px;font-weight:700}}
  .ok{{color:var(--brand)}} .warn{{color:var(--warn)}} .err{{color:#ef4444}}
  :is(button,.acct-wrap):focus-visible{{outline:3px solid #93c5fd;outline-offset:3px;border-radius:14px}}
  .sr{{position:absolute;left:-9999px}}
</style>
</head>
<body>
  <main class="card" role="main" aria-labelledby="title">
    <div class="bank">
      <img src="{logo_url}" alt="à¸˜à¸™à¸²à¸„à¸²à¸£à¸à¸ªà¸´à¸à¸£à¹„à¸—à¸¢" class="bank-logo" loading="lazy" decoding="async"
           referrerpolicy="no-referrer"
           onerror="this.remove();document.getElementById('kbank-fallback').style.display='block';">
      <div>
        <div id="title" class="bank-title">à¸˜à¸™à¸²à¸„à¸²à¸£à¸à¸ªà¸´à¸à¸£à¹„à¸—à¸¢</div>
        <div class="subtitle" aria-hidden="true">à¸˜à¸™à¸²à¸„à¸²à¸£à¸à¸ªà¸´à¸à¸£à¹„à¸—à¸¢</div>
        <div id="kbank-fallback" class="subtitle" style="display:none">KBank</div>
      </div>
    </div>

    <div class="acct-wrap" tabindex="0" aria-live="polite" aria-atomic="true">
      <div class="label">à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µ</div>
      <div id="acct" class="acct" data-raw="{acct}"></div>
    </div>

    <p class="help">à¹à¸•à¸° â€œà¸„à¸±à¸”à¸¥à¸­à¸à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µâ€ à¹à¸¥à¹‰à¸§à¸ªà¸¥à¸±à¸šà¹„à¸›à¸—à¸µà¹ˆà¹à¸­à¸›à¸˜à¸™à¸²à¸„à¸²à¸£à¹€à¸žà¸·à¹ˆà¸­à¸§à¸²à¸‡à¹à¸¥à¸°à¹‚à¸­à¸™à¹€à¸‡à¸´à¸™</p>

    <div class="btns">
      <button id="copyBtn" class="primary" aria-label="à¸„à¸±à¸”à¸¥à¸­à¸à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µ">à¸„à¸±à¸”à¸¥à¸­à¸à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µ</button>
      <button id="closeBtn" class="secondary" aria-label="à¸›à¸´à¸”à¸«à¸™à¹‰à¸²à¸™à¸µà¹‰">à¸›à¸´à¸”à¸«à¸™à¹‰à¸²à¸™à¸µà¹‰</button>
    </div>

    <div id="status" class="status warn">à¸à¸³à¸¥à¸±à¸‡à¹€à¸•à¸£à¸µà¸¢à¸¡à¸„à¸±à¸”à¸¥à¸­à¸à¹ƒà¸«à¹‰à¸­à¸±à¸•à¹‚à¸™à¸¡à¸±à¸•à¸´â€¦</div>
    <p class="help" style="margin-top:14px">à¹€à¸„à¸¥à¹‡à¸”à¸¥à¸±à¸š: à¸–à¹‰à¸²à¸„à¸±à¸”à¸¥à¸­à¸à¹„à¸¡à¹ˆà¸•à¸´à¸” à¹ƒà¸«à¹‰à¸à¸”à¸›à¸¸à¹ˆà¸¡ â€œà¸„à¸±à¸”à¸¥à¸­à¸à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µâ€ à¸­à¸µà¸à¸„à¸£à¸±à¹‰à¸‡</p>
    <p class="sr" id="rawValue">{acct}</p>
  </main>

<script>
(function() {{
  const acctEl   = document.getElementById('acct');
  const statusEl = document.getElementById('status');
  const copyBtn  = document.getElementById('copyBtn');
  const closeBtn = document.getElementById('closeBtn');
  const raw      = (acctEl.getAttribute('data-raw') || '').trim();

  function formatReadable(v) {{
    const digits = v.replace(/\\D+/g,'');
    if (digits.length === 10) {{
      return digits.replace(/(\\d{{3}})(\\d)(\\d{{5}})(\\d)/, '$1-$2-$3-$4'); // 123-4-56789-0
    }}
    return digits.replace(/(\\d{{4}})(?=\\d)/g, '$1 ').trim();
  }}

  acctEl.textContent = formatReadable(raw);

  async function doCopy() {{
    const value = raw;
    try {{
      if (navigator.clipboard?.writeText) {{
        await navigator.clipboard.writeText(value);
      }} else {{
        const ta = document.createElement('textarea');
        ta.value = value; ta.style.position='fixed'; ta.style.opacity='0';
        document.body.appendChild(ta); ta.focus(); ta.select(); document.execCommand('copy'); ta.remove();
      }}
      statusEl.textContent = 'à¸„à¸±à¸”à¸¥à¸­à¸à¹à¸¥à¹‰à¸§ âœ“ à¸™à¸³à¹„à¸›à¸§à¸²à¸‡à¹ƒà¸™à¹à¸­à¸›à¸˜à¸™à¸²à¸„à¸²à¸£à¹„à¸”à¹‰à¹€à¸¥à¸¢';
      statusEl.className = 'status ok';
    }} catch(e) {{
      statusEl.textContent = 'à¸„à¸±à¸”à¸¥à¸­à¸à¹„à¸¡à¹ˆà¸ªà¸³à¹€à¸£à¹‡à¸ˆ à¸à¸£à¸¸à¸“à¸²à¸à¸”à¸›à¸¸à¹ˆà¸¡ â€œà¸„à¸±à¸”à¸¥à¸­à¸à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µâ€ à¸­à¸µà¸à¸„à¸£à¸±à¹‰à¸‡';
      statusEl.className = 'status err';
    }}
  }}

  function robustClose() {{
    window.close();
    setTimeout(() => {{
      if (history.length > 1) {{
        history.back();
        return;
      }}
      const selfWin = window.open('', '_self');
      if (selfWin) {{
        try {{ selfWin.close(); }} catch(_) {{}}
      }}
      try {{
        location.replace('about:blank');
        statusEl.textContent = 'à¸›à¸´à¸”à¹à¸—à¹‡à¸šà¸™à¸µà¹‰à¹„à¸”à¹‰à¹€à¸¥à¸¢';
        statusEl.className = 'status warn';
      }} catch(_) {{}}
    }}, 150);
  }}

  copyBtn.addEventListener('click', doCopy);
  closeBtn.addEventListener('click', robustClose);
  doCopy();
}})();
</script>
</body>
</html>"""
    resp = make_response(html, 200)
    resp.headers["Content-Type"] = "text/html; charset=utf-8"
    resp.headers["ngrok-skip-browser-warning"] = "true"
    return resp






def flex_register_success(cid: int):
    return FlexSendMessage(
        alt_text="à¸¥à¸‡à¸—à¸°à¹€à¸šà¸µà¸¢à¸™à¸ªà¸³à¹€à¸£à¹‡à¸ˆ",
        contents={
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "10px",
                "backgroundColor": "#111827",
                "cornerRadius": "12px",
                "spacing": "sm",
                "contents": [
                    {"type": "text", "text": "âœ… à¸¥à¸‡à¸—à¸°à¹€à¸šà¸µà¸¢à¸™à¸ªà¸³à¹€à¸£à¹‡à¸ˆ", "weight": "bold", "size": "md", "align": "center", "color": "#22C55E"},
                    {"type": "text", "text": f"ðŸŽ« ID à¸‚à¸­à¸‡à¸„à¸¸à¸“à¸„à¸·à¸­ {cid}", "size": "sm", "weight": "bold", "align": "center", "color": "#FACC15"},
                    {"type": "text", "text": "à¸žà¸´à¸¡à¸žà¹Œ C à¹€à¸žà¸·à¹ˆà¸­à¸”à¸¹à¸šà¸±à¸•à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸", "size": "xs", "align": "center", "color": "#9CA3AF"}
                ]
            }
        }
    )


from linebot.models import FlexSendMessage

def flex_summary(st, event=None):
    bets = list(st["bet_index"].values())
    rows = []

    if not bets:
        rows.append({
            "type": "text",
            "text": "âŒ à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸šà¸´à¸¥",
            "size": "md",
            "align": "center",
            "color": "#9CA3AF",
            "weight": "bold"
        })
    else:
        # ===== à¸«à¸±à¸§à¸•à¸²à¸£à¸²à¸‡ =====
        rows.append({
            "type": "box", "layout": "horizontal", "contents": [
                {"type": "text", "text": "ðŸ‘¤ à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™", "flex": 5, "size": "sm", "weight": "bold", "color": "#F9FAFB"},
                {"type": "text", "text": "ðŸš€ à¸ªà¸¹à¸‡/à¸•à¹ˆà¸³", "flex": 3, "size": "sm", "align": "center", "weight": "bold", "color": "#F9FAFB"},
                {"type": "text", "text": "ðŸ’° à¸¢à¸­à¸”à¹€à¸¥à¹ˆà¸™", "flex": 3, "size": "sm", "align": "end", "weight": "bold", "color": "#F9FAFB"},
            ]
        })
        rows.append({"type": "separator", "margin": "sm", "color": "#6B7280"})

        # ===== à¸£à¸²à¸¢à¸à¸²à¸£à¸šà¸´à¸¥ =====
        for i, b in enumerate(bets):
            bg_color = "#1E293B"   # à¹ƒà¸Šà¹‰à¸ªà¸µà¹€à¸”à¸µà¸¢à¸§à¸—à¸¸à¸à¹à¸–à¸§
            name = b["name"]
            if b["side"] == "HI":
                side_display = "âœ… à¸ªà¸¹à¸‡"
                side_color = "#22C55E"
            else:
                side_display = "âŒ à¸•à¹ˆà¸³"
                side_color = "#EF4444"

            # à¸à¸¥à¹ˆà¸­à¸‡à¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¸¥à¸¹à¸à¸„à¹‰à¸²
            rows.append({
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {
                        "type": "box",
                        "layout": "horizontal",
                        "backgroundColor": bg_color,
                        "cornerRadius": "6px",
                        "paddingAll": "6px",
                        "contents": [
                            {"type": "text", "text": name, "flex": 5, "size": "sm", "color": "#E5E7EB"},
                            {"type": "text", "text": side_display, "flex": 3, "size": "sm", "align": "center", "color": side_color},
                            {"type": "text", "text": fmt(b["amount"]), "flex": 3, "size": "sm", "align": "end", "color": "#FACC15"},
                        ]
                    },
                    # ==== à¹€à¸ªà¹‰à¸™à¸„à¸±à¹ˆà¸™à¹ƒà¸•à¹‰à¹à¸•à¹ˆà¸¥à¸°à¸Šà¸·à¹ˆà¸­ ====
                    {"type": "separator", "color": "#334155", "margin": "xs"}
                ]
            })

    # ===== Flex Message =====
    return FlexSendMessage(
        alt_text=f"ðŸ“‹ à¸ªà¸£à¸¸à¸›à¸à¸²à¸£à¹à¸—à¸‡ à¸„à¸¹à¹ˆà¸—à¸µà¹ˆ {st['pairNo']}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#111827"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "0px",
                "contents": [
                    # à¸ªà¹ˆà¸§à¸™à¸«à¸±à¸§
                    {
                        "type": "box",
                        "layout": "vertical",
                        "paddingAll": "14px",
                        "backgroundColor": "#22C55E",
                        "contents": [{
                            "type": "text",
                            "text": f"ðŸ“Š à¸ªà¸£à¸¸à¸›à¸à¸²à¸£à¹à¸—à¸‡ à¸£à¸­à¸š {st['pairNo']} ({len(bets)})",
                            "weight": "bold",
                            "align": "center",
                            "size": "lg",
                            "color": "#FFFFFF"
                        }]
                    },
                    # à¸ªà¹ˆà¸§à¸™à¸•à¸²à¸£à¸²à¸‡
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#1E293B",
                        "paddingAll": "12px",
                        "spacing": "sm",
                        "contents": rows
                    },
                    # à¸ªà¹ˆà¸§à¸™à¸—à¹‰à¸²à¸¢
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#0F172A",
                        "paddingAll": "10px",
                        "contents": [
                            {"type": "text",
                             "text": f"à¸£à¸§à¸¡à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸” {len(bets)} à¸šà¸´à¸¥",
                             "align": "end",
                             "size": "sm",
                             "color": "#E5E7EB"}
                        ]
                    }
                ]
            }
        }
    )



_admin_ids_lock = threading.RLock()
ADMINS_JSON = os.path.join(DATA_DIR, "admins.json")

def _dedupe_admin_ids(ids):
    """à¸„à¸·à¸™ list à¹à¸­à¸”à¸¡à¸´à¸™à¹à¸šà¸šà¸•à¸±à¸”à¸‹à¹‰à¸³ à¹à¸•à¹ˆà¸„à¸‡à¸¥à¸³à¸”à¸±à¸šà¹€à¸”à¸´à¸¡"""
    seen = set()
    out = []
    for x in ids or []:
        x = (x or "").strip()
        if not x or x in seen:
            continue
        seen.add(x)
        out.append(x)
    return out

def save_admins_persist():
    """à¸šà¸±à¸™à¸—à¸¶à¸à¸£à¸²à¸¢à¸Šà¸·à¹ˆà¸­à¹à¸­à¸”à¸¡à¸´à¸™à¸¥à¸‡à¹„à¸Ÿà¸¥à¹Œ data/admins.json à¹€à¸žà¸·à¹ˆà¸­à¹ƒà¸«à¹‰ restart à¹à¸¥à¹‰à¸§à¹„à¸¡à¹ˆà¸«à¸²à¸¢"""
    try:
        with _admin_ids_lock:
            payload = {"admins": _dedupe_admin_ids(ADMIN_IDS)}
        _atomic_write_json(ADMINS_JSON, payload)
    except Exception:
        try:
            app.logger.exception("save_admins_persist failed")
        except Exception:
            pass

def load_admins_persist():
    """à¹‚à¸«à¸¥à¸”à¸£à¸²à¸¢à¸Šà¸·à¹ˆà¸­à¹à¸­à¸”à¸¡à¸´à¸™à¸ˆà¸²à¸ data/admins.json à¸¡à¸²à¸£à¸§à¸¡à¸à¸±à¸š ADMIN_IDS à¹ƒà¸™ .env"""
    try:
        if not os.path.exists(ADMINS_JSON):
            return
        with open(ADMINS_JSON, "rb") as f:
            data = _loads_bytes(f.read())
        disk_admins = data.get("admins", []) if isinstance(data, dict) else data
        with _admin_ids_lock:
            for admin_uid in _dedupe_admin_ids(disk_admins):
                if admin_uid not in ADMIN_IDS:
                    ADMIN_IDS.append(admin_uid)
            ADMIN_IDS[:] = _dedupe_admin_ids(ADMIN_IDS)
    except Exception:
        try:
            app.logger.exception("load_admins_persist failed")
        except Exception:
            pass

def is_admin(uid):
    with _admin_ids_lock:
        return uid in ADMIN_IDS

def add_admin(uid):
    """à¹€à¸žà¸´à¹ˆà¸¡à¹à¸­à¸”à¸¡à¸´à¸™à¹à¸¥à¸°à¸šà¸±à¸™à¸—à¸¶à¸à¸–à¸²à¸§à¸£ à¸„à¸·à¸™ True à¸–à¹‰à¸²à¹€à¸žà¸´à¹ˆà¸¡à¹ƒà¸«à¸¡à¹ˆ / False à¸–à¹‰à¸²à¸¡à¸µà¸­à¸¢à¸¹à¹ˆà¹à¸¥à¹‰à¸§"""
    with _admin_ids_lock:
        if uid in ADMIN_IDS:
            return False
        ADMIN_IDS.append(uid)
        ADMIN_IDS[:] = _dedupe_admin_ids(ADMIN_IDS)
    save_admins_persist()
    return True

def remove_admin(uid):
    """à¸¥à¸šà¹à¸­à¸”à¸¡à¸´à¸™à¹à¸¥à¸°à¸šà¸±à¸™à¸—à¸¶à¸à¸–à¸²à¸§à¸£ à¸„à¸·à¸™ True à¸–à¹‰à¸²à¸¥à¸šà¸ªà¸³à¹€à¸£à¹‡à¸ˆ / False à¸–à¹‰à¸²à¹„à¸¡à¹ˆà¸žà¸š"""
    with _admin_ids_lock:
        if uid not in ADMIN_IDS:
            return False
        ADMIN_IDS.remove(uid)
    save_admins_persist()
    return True

# à¹‚à¸«à¸¥à¸”à¹à¸­à¸”à¸¡à¸´à¸™à¸—à¸µà¹ˆà¹€à¸„à¸¢à¹€à¸žà¸´à¹ˆà¸¡à¸œà¹ˆà¸²à¸™à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¹ƒà¸™ LINE à¹ƒà¸«à¹‰à¸à¸¥à¸±à¸šà¸¡à¸²à¸«à¸¥à¸±à¸‡ restart/deploy
load_admins_persist()

def get_user_by_cid(cid_int):
    with with_users_lock():
        for u in users.values():
            if u["cid"] == cid_int:
                return u
    return None

def register_customer_by_uid(src, target_uid):
    """à¸ªà¸¡à¸±à¸„à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸à¹ƒà¸«à¹‰ target_uid à¹à¸¥à¸°à¸„à¸·à¸™ (user_dict, created_new: bool)"""
    global nextCustomerId
    with with_users_lock():
        if target_uid in users:
            return users[target_uid], False
        name, pic = get_profile_display(src, target_uid)
        users[target_uid] = {
            "uid": target_uid,
            "cid": nextCustomerId,
            "name": name,
            "pictureUrl": pic,
            "credit": 0,
        }
        nextCustomerId += 1
        save_users_persist()
        return users[target_uid], True

def process_credit_command(text, uid):
    if not is_admin(uid):
        return "à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™"
    m = re.match(r"^@([^\s]+)\s*/\s*(\d+)$", text)
    if not m: return "à¸£à¸¹à¸›à¹à¸šà¸šà¸„à¸³à¸ªà¸±à¹ˆà¸‡à¹„à¸¡à¹ˆà¸–à¸¹à¸à¸•à¹‰à¸­à¸‡ (à¸•à¸±à¸§à¸­à¸¢à¹ˆà¸²à¸‡: @à¸ªà¸¡à¸Šà¸²à¸¢/500)"
    target_name, amt = m.group(1), int(m.group(2))

    with with_users_lock():
        target_user = next((u for u in users.values() if u["name"] == target_name), None)
        if not target_user:
            return f"à¹„à¸¡à¹ˆà¸žà¸šà¸œà¸¹à¹‰à¹ƒà¸Šà¹‰ {target_name}"
        target_user["credit"] = target_user.get("credit", 0) + amt
        save_users_persist()
        return (f"à¹€à¸•à¸´à¸¡à¹€à¸„à¸£à¸”à¸´à¸• {fmt(amt)} à¸šà¸²à¸—  "
                f"ID : {target_user['cid']}  {target_user['name']}  "
                f"à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­ {fmt(target_user['credit'])} à¸šà¸²à¸—")

def save_score_history_latest(state, round_no, camp, code):
    # à¸¥à¸šà¸œà¸¥à¸£à¸­à¸šà¹€à¸”à¸´à¸¡à¸­à¸­à¸à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”
    state["score_history"] = [
        h for h in state.get("score_history", [])
        if h.get("round") != round_no
    ]

    # à¹ƒà¸ªà¹ˆà¸œà¸¥à¸¥à¹ˆà¸²à¸ªà¸¸à¸”à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™
    state["score_history"].append({
        "round": round_no,
        "camp": camp,
        "code": code,
        "updated_at": datetime.now().isoformat()
    })






# ====== MESSAGE HANDLER ======
@handler.add(MessageEvent, message=TextMessage)
def on_message(event: MessageEvent):
    global nextCustomerId

    uid = event.source.user_id
    gid = getattr(event.source, "group_id", None)
    key = room_key(event.source)
    
    # [FIXED] à¸à¸³à¸«à¸™à¸” text à¸—à¸µà¹ˆà¸™à¸µà¹ˆà¸„à¸£à¸±à¹‰à¸‡à¹€à¸”à¸µà¸¢à¸§
    text = (event.message.text or "").strip()

    # à¸à¸±à¸™ LINE retry / webhook à¸‹à¹‰à¸³: message id à¹€à¸”à¸´à¸¡à¸•à¹‰à¸­à¸‡à¹„à¸¡à¹ˆà¸–à¸¹à¸à¸›à¸£à¸°à¸¡à¸§à¸¥à¸œà¸¥à¸‹à¹‰à¸³
    if already_processed_message(getattr(event.message, "id", None)):
        return

    if not in_group_or_room(event.source):
     return

    # Group allow/deny/ban
    if gid:
        if gid in BANNED_GROUPS or gid in DENY_GROUP_IDS:
            return
        if not is_allowed_group(gid):
            return
        if _locked_group(gid) and not is_admin(uid):
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("à¸£à¸°à¸šà¸š: à¸à¸¥à¸¸à¹ˆà¸¡à¸à¸³à¸¥à¸±à¸‡à¸¥à¹‡à¸­à¸à¸”à¸²à¸§à¸™à¹Œà¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§ à¸•à¸´à¸”à¸•à¹ˆà¸­à¹à¸­à¸”à¸¡à¸´à¸™à¹€à¸žà¸·à¹ˆà¸­à¸›à¸¥à¸”à¸¥à¹‡à¸­à¸"))
            return

    # user ban/mute
    if uid in BANNED_UIDS:
        return
    if MUTED_UNTIL.get(uid, 0) > _now():
        if not _notice_throttled(uid):
            safe_reply(event, TextSendMessage("à¸£à¸°à¸šà¸š: à¸„à¸¸à¸“à¸–à¸¹à¸à¸ˆà¸³à¸à¸±à¸”à¸à¸²à¸£à¸ªà¹ˆà¸‡à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§ (anti-spam)"))
        return

    # rate limit room/user
    if not rl.allow(f"room:{key}", RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD):
        return
    if not rl.allow(f"uid:{uid}:burst", RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD) or \
       not rl.allow(f"uid:{uid}:day", RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD):
        STRIKES[uid] = STRIKES.get(uid, 0) + 1
        if STRIKES[uid] >= ABUSE_STRIKE_TO_MUTE:
            MUTED_UNTIL[uid] = _now() + MUTE_SECONDS_DEFAULT
            STRIKES[uid] = 0
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage(f"à¸£à¸°à¸šà¸š: à¸¡à¸´à¸§à¸—à¹Œ {MUTE_SECONDS_DEFAULT} à¸§à¸´à¸™à¸²à¸—à¸µ à¹€à¸™à¸·à¹ˆà¸­à¸‡à¸ˆà¸²à¸à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸–à¸µà¹ˆà¸œà¸´à¸”à¸›à¸à¸•à¸´"))
        else:
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("à¸£à¸°à¸šà¸š: à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸–à¸µà¹ˆà¹€à¸à¸´à¸™à¸à¸³à¸«à¸™à¸” à¸Šà¹ˆà¸§à¸¢à¹€à¸§à¹‰à¸™à¸Šà¹ˆà¸§à¸‡à¸«à¸™à¹ˆà¸­à¸¢à¸™à¸°"))
        return

    # cache for unsend monitor
    msgCache[event.message.id] = {"text": (event.message.text or ""), "ts": time.time()}
    now = time.time()
    if len(msgCache) > 4000:
        for k, v in list(msgCache.items()):
            if now - v["ts"] > CACHE_TTL_SEC: msgCache.pop(k, None)

    # [FIXED] à¸£à¸§à¸šà¸£à¸§à¸¡à¸•à¸£à¸£à¸à¸°à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”à¸—à¸µà¹ˆà¹€à¸à¸µà¹ˆà¸¢à¸§à¸‚à¹‰à¸­à¸‡à¸à¸±à¸š Room State (st) à¹„à¸§à¹‰à¹ƒà¸™ Lock à¹€à¸”à¸µà¸¢à¸§
    with with_rooms_lock():
        if key not in rooms:
            rooms[key] = start_state()
        st = rooms[key]

        # [FIXED] à¸•à¸£à¸§à¸ˆà¸ªà¸­à¸š Cooldown à¸ à¸²à¸¢à¹ƒà¸™ Lock
        if not is_admin(uid):
            whitelist = {"add", "c", "à¸à¸•", "à¸šà¸Š", "x", "xx", "x*", "à¸–à¸­à¸™", "à¸§à¸´à¸˜à¸µà¹€à¸¥à¹ˆà¸™", "à¸§à¸´à¸˜à¸µà¸à¸²à¸£à¹€à¸¥à¹ˆà¸™", "à¹€à¸¥à¹ˆà¸™"}
            text_preview = text.lower()
            head = text_preview.split(" ", 1)[0] if text_preview else ""
            scope_key = f"{uid}:{key}"

            if head not in whitelist:
                if not _should_reply_now(scope_key):
                    # à¹€à¸‡à¸µà¸¢à¸š: à¹„à¸¡à¹ˆà¸•à¸­à¸šà¹à¸¥à¸°à¹„à¸¡à¹ˆà¸›à¸£à¸°à¸¡à¸§à¸¥à¸œà¸¥à¸„à¸³à¸ªà¸±à¹ˆà¸‡ à¹€à¸žà¸·à¹ˆà¸­à¸à¸±à¸™à¸£à¸±à¸§à¸ˆà¸£à¸´à¸‡ à¹†
                    return
        # --- à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸¥à¹‰à¸²à¸‡à¸à¸³à¹„à¸£à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸” (à¹€à¸‰à¸žà¸²à¸° Admin) ---
        if R_CLEAR_PROFIT.match(text):
            if uid not in ADMIN_IDS:
                return  # à¹„à¸¡à¹ˆà¹ƒà¸Šà¹ˆà¹à¸­à¸”à¸¡à¸´à¸™à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¸•à¸­à¸šà¹‚à¸•à¹‰
            
            with with_rooms_lock(): # à¹ƒà¸Šà¹‰ lock à¹€à¸žà¸·à¹ˆà¸­à¸„à¸§à¸²à¸¡à¸›à¸¥à¸­à¸”à¸ à¸±à¸¢à¸‚à¸­à¸‡à¸‚à¹‰à¸­à¸¡à¸¹à¸¥
                METRICS["profit_sum"] = 0
                METRICS["loss_sum"] = 0
                
            now = datetime.now().strftime("%H:%M:%S")
            reply_msg = (
                "âœ… à¸£à¸µà¹€à¸‹à¹‡à¸•à¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¸à¸³à¹„à¸£à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”à¹€à¸£à¸µà¸¢à¸šà¸£à¹‰à¸­à¸¢à¹à¸¥à¹‰à¸§\n"
                f"ðŸ•’ à¹€à¸§à¸¥à¸²: {now}\n"
                "ðŸ’° à¸¢à¸­à¸”à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­à¸›à¸±à¸ˆà¸ˆà¸¸à¸šà¸±à¸™: 0"
            )
            line_bot_api.reply_message(event.reply_token, TextSendMessage(text=reply_msg))
            return
        


        # ===== à¸§à¸´à¸˜à¸µà¹€à¸¥à¹ˆà¸™ / à¹€à¸¥à¹ˆà¸™à¸¢à¸±à¸‡à¹„à¸‡ / à¹€à¸¥à¹ˆà¸™à¹„à¸‡ / à¸§à¸´à¸˜à¸µà¸à¸²à¸£à¹€à¸¥à¹ˆà¸™ / à¹€à¸¥à¹ˆà¸™à¹à¸šà¸šà¹ƒà¸” =====
        t = text.strip()
        t2 = " ".join(t.split())  # à¸šà¸µà¸šà¸Šà¹ˆà¸­à¸‡à¸§à¹ˆà¸²à¸‡à¸‹à¹‰à¸³à¹ƒà¸«à¹‰à¹€à¸«à¸¥à¸·à¸­ 1

        if t in PLAY_HELP_COMMANDS or t2 in PLAY_HELP_COMMANDS:
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return

        # à¸à¸£à¸“à¸µà¸œà¸¹à¹‰à¹ƒà¸Šà¹‰à¸žà¸´à¸¡à¸žà¹Œà¹à¸šà¸šà¸¡à¸µà¹€à¸§à¹‰à¸™à¸§à¸£à¸£à¸„ à¹€à¸Šà¹ˆà¸™ "à¹€à¸¥à¹ˆà¸™ à¸¢à¸±à¸‡à¹„à¸‡"
        if t2.startswith("à¹€à¸¥à¹ˆà¸™") and ("à¸¢à¸±à¸‡à¹„à¸‡" in t2 or "à¹„à¸‡" in t2 or "à¹à¸šà¸šà¹ƒà¸”" in t2):
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return

        if t2.startswith("à¸§à¸´à¸˜à¸µ") and ("à¹€à¸¥à¹ˆà¸™" in t2):
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return
    

        # ===== Admin: add/del with @mention or Uxxxxxxxx + optional PIN =====
        # à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¸—à¸±à¹‰à¸‡: admin add @à¸Šà¸·à¹ˆà¸­ / admin @à¸Šà¸·à¹ˆà¸­ / à¹€à¸žà¸´à¹ˆà¸¡à¹à¸­à¸”à¸¡à¸´à¸™ @à¸Šà¸·à¹ˆà¸­à¹„à¸¥à¸™à¹Œ
        if R_ADMIN_ADD.match(text):
            if not is_admin(uid):
                return

            target_uid = first_mentioned_uid(event)

            # à¹€à¸œà¸·à¹ˆà¸­à¸à¸£à¸“à¸µà¸žà¸´à¸¡à¸žà¹Œ UID à¸•à¸£à¸‡ à¹† à¹€à¸Šà¹ˆà¸™: à¹€à¸žà¸´à¹ˆà¸¡à¹à¸­à¸”à¸¡à¸´à¸™ Uxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
            if not target_uid:
                m = re.search(r"\b([Uu][0-9a-f]{32})\b", text)
                if m:
                    target_uid = m.group(1)

            if not target_uid:
                safe_reply(event, TextSendMessage(
                    "âŒ à¸à¸£à¸¸à¸“à¸²à¹à¸—à¹‡à¸à¸Šà¸·à¹ˆà¸­à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰à¸—à¸µà¹ˆà¸•à¹‰à¸­à¸‡à¸à¸²à¸£à¹€à¸žà¸´à¹ˆà¸¡\nà¸•à¸±à¸§à¸­à¸¢à¹ˆà¸²à¸‡: à¹€à¸žà¸´à¹ˆà¸¡à¹à¸­à¸”à¸¡à¸´à¸™ @à¸Šà¸·à¹ˆà¸­à¹„à¸¥à¸™à¹Œ"
                ))
                return

            target_name, _ = get_profile_display(event.source, target_uid)

            if add_admin(target_uid):
                safe_reply(event, TextSendMessage(
                    f"âœ… à¹€à¸žà¸´à¹ˆà¸¡à¹à¸­à¸”à¸¡à¸´à¸™à¸ªà¸³à¹€à¸£à¹‡à¸ˆ\nðŸ‘¤ {target_name}"
                ))
            else:
                safe_reply(event, TextSendMessage(
                    f"â„¹ï¸ à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰à¸™à¸µà¹‰à¹€à¸›à¹‡à¸™à¹à¸­à¸”à¸¡à¸´à¸™à¸­à¸¢à¸¹à¹ˆà¹à¸¥à¹‰à¸§\nðŸ‘¤ {target_name}"
                ))
            return

        if R_ADMIN_DEL.match(text):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return
            target_uid = first_mentioned_uid(event)
            if not target_uid:
                m = re.search(r"\b([Uu][0-9a-f]{32})\b", text)
                if m: target_uid = m.group(1)
            if not target_uid:
                safe_reply(event, TextSendMessage("à¹‚à¸›à¸£à¸”à¹à¸—à¹‡à¸à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰ à¸«à¸£à¸·à¸­à¸£à¸°à¸šà¸¸ userId à¸—à¸µà¹ˆà¸‚à¸¶à¹‰à¸™à¸•à¹‰à¸™à¸”à¹‰à¸§à¸¢ U...")); return
            pin = _admin_auth_pin(text)
            if ADMIN_PIN and not compare_digest(pin, ADMIN_PIN):
                safe_reply(event, TextSendMessage("PIN à¹„à¸¡à¹ˆà¸–à¸¹à¸à¸•à¹‰à¸­à¸‡")); return
            if remove_admin(target_uid):
                safe_reply(event, TextSendMessage("à¸¥à¸šà¹à¸­à¸”à¸¡à¸´à¸™à¸ªà¸³à¹€à¸£à¹‡à¸ˆ âœ“"))
            else:
                safe_reply(event, TextSendMessage("à¹„à¸¡à¹ˆà¸žà¸šà¹„à¸­à¸”à¸µà¸™à¸µà¹‰à¹ƒà¸™à¸£à¸²à¸¢à¸Šà¸·à¹ˆà¸­à¹à¸­à¸”à¸¡à¸´à¸™"))
            return
        
        # ===== Admin: list (à¹€à¸Šà¹‡à¸„à¹à¸­à¸”à¸¡à¸´à¸™ / admin list) =====
        if R_ADMIN_LIST.match(text):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return
            with _admin_ids_lock:
                current_admins = list(ADMIN_IDS)
            if not current_admins:
                safe_reply(event, TextSendMessage("â„¹ï¸ à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¹à¸­à¸”à¸¡à¸´à¸™à¹ƒà¸™à¸£à¸°à¸šà¸š")); return
            lines = ["ðŸ‘‘ à¸£à¸²à¸¢à¸Šà¸·à¹ˆà¸­à¹à¸­à¸”à¸¡à¸´à¸™à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”\n"]
            for i, a_uid in enumerate(current_admins, 1):
                try:
                    profile = line_bot_api.get_profile(a_uid)
                    a_name = profile.display_name
                except Exception:
                    a_name = users.get(a_uid, {}).get("name", "(à¹„à¸¡à¹ˆà¸—à¸£à¸²à¸šà¸Šà¸·à¹ˆà¸­)")
                lines.append(f"{i}. {a_name}\n   ID: {a_uid}")
            lines.append(f"\nà¸£à¸§à¸¡ {len(current_admins)} à¸„à¸™")
            safe_reply(event, TextSendMessage("\n".join(lines)))
            return

        # ===== Group ID (gid) =====
        if re.match(r"^gid\b", text, re.IGNORECASE):
            if not gid:
                safe_reply(event, TextSendMessage("à¹ƒà¸Šà¹‰à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹ƒà¸™à¸à¸¥à¸¸à¹ˆà¸¡/à¸«à¹‰à¸­à¸‡"))
                return
            safe_reply(event, TextSendMessage(f"GID à¸‚à¸­à¸‡à¸à¸¥à¸¸à¹ˆà¸¡à¸™à¸µà¹‰: {gid}"))
            return


        # ==== à¸”à¸¹à¸•à¸²à¸£à¸²à¸‡à¸£à¸²à¸¢à¸à¸²à¸£à¹€à¸”à¸´à¸¡à¸žà¸±à¸™ (cm â€” à¹€à¸‰à¸žà¸²à¸°à¸à¸¥à¸¸à¹ˆà¸¡à¸«à¸¥à¸±à¸‡à¸šà¹‰à¸²à¸™) ====
        if text.lower() == "cm":
            if not gid or not is_backoffice_group_id(gid):
                return
            snapshot = [(rk, stx.copy()) for rk, stx in rooms.items()]  # shallow à¸à¹‡à¸žà¸­
            all_bets, total_hi, total_lo = [], 0, 0
            hi_count, lo_count = 0, 0
            active_round_labels = []
            seen_round_labels = set()

            for rk, stx in snapshot:
                pair_no = stx.get("pairNo", 0)
                camp_name = current_camp(stx)
                round_label = f"{camp_name} â€¢ à¸£à¸­à¸š {pair_no}"
                if pair_no and round_label not in seen_round_labels:
                    active_round_labels.append(round_label)
                    seen_round_labels.add(round_label)

                for b in stx.get("bet_index", {}).values():
                    all_bets.append({
                        "name": b["name"],
                        "side": b["side"],
                        "amount": b["amount"],
                        "pairNo": pair_no,
                        "camp": camp_name,
                    })
                    if b["side"] == "HI":
                        total_hi += b["amount"]
                        hi_count += 1
                    else:
                        total_lo += b["amount"]
                        lo_count += 1

            if not all_bets:
                safe_reply(event, TextSendMessage("(à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸šà¸´à¸¥à¹ƒà¸™à¸£à¸°à¸šà¸š)"))
                return

            title_text = "à¸•à¸²à¸£à¸²à¸‡à¸šà¸´à¸¥à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”"
            if len(active_round_labels) == 1:
                title_text = f"à¸•à¸²à¸£à¸²à¸‡à¸šà¸´à¸¥à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸” ({active_round_labels[0]})"
            elif len(active_round_labels) > 1:
                title_text = "à¸•à¸²à¸£à¸²à¸‡à¸šà¸´à¸¥à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸” (à¸«à¸¥à¸²à¸¢à¸„à¹ˆà¸²à¸¢/à¸«à¸¥à¸²à¸¢à¸£à¸­à¸š)"

            rows = [
                {"type":"box","layout":"vertical","spacing":"xs","contents":[
                    {"type":"text","text":title_text,"weight":"bold","align":"center","size":"md","wrap":True},
                    {"type":"text","text":f"à¸ˆà¸³à¸™à¸§à¸™à¸šà¸´à¸¥à¸ªà¸¹à¸‡ {hi_count} à¸šà¸´à¸¥ â€¢ à¸ˆà¸³à¸™à¸§à¸™à¸šà¸´à¸¥à¸•à¹ˆà¸³ {lo_count} à¸šà¸´à¸¥","size":"sm","align":"center","weight":"bold","wrap":True,
                     "color":"#1565C0" if lo_count == 0 else "#374151"},
                ]},
                {"type":"separator","margin":"md"},
            ]

            if len(active_round_labels) > 1:
                rows.append({
                    "type":"box","layout":"vertical","spacing":"xs","contents":[
                        {"type":"text","text":"à¸„à¹ˆà¸²à¸¢ / à¸£à¸­à¸šà¸—à¸µà¹ˆà¹€à¸›à¸´à¸”à¸­à¸¢à¸¹à¹ˆ","size":"sm","weight":"bold","color":"#374151"},
                        *[
                            {"type":"text","text":f"â€¢ {label}","size":"xs","wrap":True,"color":"#6B7280"}
                            for label in active_round_labels[:8]
                        ]
                    ]
                })
                rows.append({"type":"separator","margin":"md"})

            rows.extend([
                {"type":"box","layout":"horizontal","spacing":"sm","contents":[
                    {"type":"text","text":"à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™","flex":5,"size":"xs","weight":"bold","wrap":True},
                    {"type":"text","text":"à¸ˆà¸³à¸™à¸§à¸™à¹€à¸”à¸´à¸¡à¸žà¸±à¸™/à¸à¸µà¹ˆà¸šà¸²à¸—","flex":5,"size":"xs","align":"center","weight":"bold","wrap":True},
                    {"type":"text","text":"à¸£à¸­à¸š","flex":2,"size":"xs","align":"center","weight":"bold","wrap":True},
                ]},
                {"type":"separator","margin":"sm"},
            ])

            def _short_name(name, limit=14):
                name = (name or "").strip()
                if len(name) <= limit:
                    return name
                return name[:limit-1].rstrip() + "â€¦"

            sorted_bets = sorted(
                all_bets,
                key=lambda x: (
                    -(x.get("amount", 0) or 0),
                    x.get("pairNo", 0),
                    x.get("camp", "") or "",
                    x.get("name", "") or "",
                )
            )

            for b in sorted_bets:
                bet_text = f'{"à¸ªà¸¹à¸‡" if b["side"]=="HI" else "à¸•à¹ˆà¸³"} {fmt(b["amount"])} à¸šà¸²à¸—'
                rows.append({"type":"box","layout":"horizontal","spacing":"sm","contents":[
                    {"type":"text","text":_short_name(b["name"]),"flex":5,"size":"xs","wrap":True},
                    {"type":"text","text":bet_text,
                     "flex":5,"size":"xs","align":"center",
                     "color":"#1565C0" if b["side"]=="HI" else "#E53935","wrap":True},
                    {"type":"text","text":str(b["pairNo"]),"flex":2,"size":"xs","align":"center","wrap":True},
                ]})
            rows.append({"type":"separator","margin":"md"})
            rows.append({"type":"text","text":f"à¸£à¸§à¸¡à¸ªà¸¹à¸‡: {fmt(total_hi)} à¸šà¸²à¸— ({hi_count} à¸šà¸´à¸¥)","size":"sm","align":"end","weight":"bold","color":"#1565C0"})
            rows.append({"type":"text","text":f"à¸£à¸§à¸¡à¸•à¹ˆà¸³: {fmt(total_lo)} à¸šà¸²à¸— ({lo_count} à¸šà¸´à¸¥)","size":"sm","align":"end","weight":"bold","color":"#E53935"})
            safe_reply(event, FlexSendMessage(
                alt_text="à¸•à¸²à¸£à¸²à¸‡à¸šà¸´à¸¥à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”",
                contents={"type":"bubble","size":"mega","body":{"type":"box","layout":"vertical","spacing":"sm","paddingAll":"12px","contents":rows}}
            ))
            return

        # ===== Moderator: ban/mute/unban/unmute =====
        m_cmd = re.match(r"^(ban|unban|mute|unmute)\b(?:\s+(.*))?$", text, re.IGNORECASE)
        if m_cmd:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return
            cmd = m_cmd.group(1).lower()
            args = (m_cmd.group(2) or "").strip()
            target_uid = first_mentioned_uid(event)
            sec = None
            if not target_uid:
                m_uid = re.match(r"^(U[0-9a-f]{32})\b(?:\s+(\d+))?$", args, re.IGNORECASE)
                if m_uid:
                    target_uid = m_uid.group(1)
                    sec = int(m_uid.group(2) or MUTE_SECONDS_DEFAULT) if cmd == "mute" else None
                else:
                    m_at = re.match(r"^@(.+?)(?:\s+(\d+))?$", args)
                    if m_at:
                        safe_reply(event, TextSendMessage("à¹‚à¸›à¸£à¸”à¹à¸—à¹‡à¸à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰à¸ˆà¸²à¸ UI à¸‚à¸­à¸‡ LINE (à¸Šà¸·à¹ˆà¸­à¹€à¸›à¹‡à¸™à¸¥à¸´à¸‡à¸à¹Œà¸ªà¸µà¸™à¹‰à¸³à¹€à¸‡à¸´à¸™)"))
                        return
            if not target_uid:
                safe_reply(event, TextSendMessage("à¸£à¸¹à¸›à¹à¸šà¸š: mute @à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰ [à¸§à¸´à¸™à¸²à¸—à¸µ] / unmute @à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰ / ban @à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰ / unban @à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰"))
                return
            if cmd == "mute":
                if sec is None:
                    m_sec = re.search(r"\b(\d+)\b$", args) if args else None
                    sec = int(m_sec.group(1)) if m_sec else MUTE_SECONDS_DEFAULT
                MUTED_UNTIL[target_uid] = _now() + max(1, sec); safe_reply(event, TextSendMessage(f"à¸¡à¸´à¸§à¸—à¹Œ {sec} à¸§à¸´à¸™à¸²à¸—à¸µà¹à¸¥à¹‰à¸§")); return
            if cmd == "unmute":
                MUTED_UNTIL.pop(target_uid, None); safe_reply(event, TextSendMessage("à¸›à¸¥à¸”à¸¡à¸´à¸§à¸—à¹Œà¹à¸¥à¹‰à¸§")); return
            if cmd == "ban":
                BANNED_UIDS.add(target_uid); safe_reply(event, TextSendMessage("à¹à¸šà¸™à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰à¹à¸¥à¹‰à¸§")); return
            if cmd == "unban":
                BANNED_UIDS.discard(target_uid); safe_reply(event, TextSendMessage("à¸›à¸¥à¸”à¹à¸šà¸™à¹à¸¥à¹‰à¸§")); return

        # ===== Admin/User: à¹€à¸Šà¹‡à¸„ UID =====
        if re.match(r"^uid\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)
            # à¸–à¹‰à¸²à¹„à¸¡à¹ˆà¹à¸—à¹‡à¸à¹ƒà¸„à¸£: à¹‚à¸Šà¸§à¹Œ UID à¸‚à¸­à¸‡à¸•à¸±à¸§à¹€à¸­à¸‡ (à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¹€à¸›à¹‡à¸™à¹à¸­à¸”à¸¡à¸´à¸™)
            if not target_uid or target_uid == uid:
                name, _ = get_profile_display(event.source, uid)
                safe_reply(event, TextSendMessage(f"UID à¸‚à¸­à¸‡à¸„à¸¸à¸“ ({name}): {uid}"))
                return
            # à¸–à¹‰à¸²à¸ˆà¸°à¸”à¸¹ UID à¸„à¸™à¸­à¸·à¹ˆà¸™ à¸•à¹‰à¸­à¸‡à¹€à¸›à¹‡à¸™à¹à¸­à¸”à¸¡à¸´à¸™
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™à¸—à¸µà¹ˆà¸”à¸¹ UID à¸„à¸™à¸­à¸·à¹ˆà¸™à¹„à¸”à¹‰")); 
                return
            name, _ = get_profile_display(event.source, target_uid)
            safe_reply(event, TextSendMessage(f"UID à¸‚à¸­à¸‡ {name}: {target_uid}"))
            return

                # ===== Backoffice (FREE): à¸”à¸¹à¸ªà¸£à¸¸à¸›/à¸à¸³à¹„à¸£à¸¥à¹ˆà¸²à¸ªà¸¸à¸” =====
        # à¹ƒà¸Šà¹‰à¹ƒà¸™à¸à¸¥à¸¸à¹ˆà¸¡à¸«à¸¥à¸±à¸‡à¸šà¹‰à¸²à¸™à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™ (à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡ push à¸¥à¸”à¹‚à¸„à¸§à¸•à¹‰à¸²)
        if gid and gid in BACKOFFICE_GROUP_IDS and re.match(r"^(?:à¸à¸³à¹„à¸£à¸¥à¹ˆà¸²à¸ªà¸¸à¸”|à¸¢à¸­à¸”|lastprofit|last)\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); 
                return
            p = load_last_settle()
            if not p:
                safe_reply(event, TextSendMessage("à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸ªà¸£à¸¸à¸›à¸œà¸¥à¸¥à¹ˆà¸²à¸ªà¸¸à¸”à¹ƒà¸™à¸£à¸°à¸šà¸š")); 
                return
            safe_reply(event, TextSendMessage(settle_payload_to_text(p)))
            return

        # ===== Helper: à¸„à¸·à¸™ escrow à¸—à¸¸à¸à¸„à¸™à¹ƒà¸™à¸«à¹‰à¸­à¸‡ =====
        def _refund_all_escrow_to_users(st):
            refunded_map = {}  # uid -> amount
            for tuid, esc_amt in list(st.get("escrow", {}).items()):
                if esc_amt > 0 and tuid in users:
                    users[tuid]["credit"] = users[tuid].get("credit", 0) + esc_amt
                    refunded_map[tuid] = esc_amt
            st["escrow"].clear()
            return refunded_map
        
        # -

        text = (event.message.text or "").strip()

        # ====== GET GROUP ID ======
        if R_GETID.match(text):
            src = event.source

            group_id = getattr(src, "group_id", None)
            room_id = getattr(src, "room_id", None)

            if group_id:
                msg = f"Group ID: {group_id}"
            elif room_id:
                msg = f"Room ID: {room_id}"
            else:
                msg = "âŒ à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹ƒà¸™à¸à¸¥à¸¸à¹ˆà¸¡à¸«à¸£à¸·à¸­à¸«à¹‰à¸­à¸‡à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™"

            safe_reply(event, TextSendMessage(text=msg))
            return


        # ==== CLEAR / RESET ====
        if re.match(r"^(clear|reset)\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return

            total_refund_sum = 0
            total_refund_users = 0

            with with_users_lock(): # [FIXED] à¹ƒà¸Šà¹‰à¹à¸„à¹ˆ with_users_lock() à¹€à¸žà¸£à¸²à¸° with_rooms_lock() à¸„à¸¥à¸¸à¸¡à¸­à¸¢à¸¹à¹ˆà¹à¸¥à¹‰à¸§
                if re.search(r"\ball\b", text, re.IGNORECASE):
                    # à¹€à¸„à¸¥à¸µà¸¢à¸£à¹Œà¸—à¸±à¹‰à¸‡à¸£à¸°à¸šà¸š â€” à¸„à¸·à¸™ escrow à¸—à¸¸à¸à¸«à¹‰à¸­à¸‡
                    for rk in list(rooms.keys()):
                        stx = rooms[rk]
                        refunded_map = _refund_all_escrow_to_users(stx)
                        total_refund_sum += sum(refunded_map.values())
                        total_refund_users += len(refunded_map)
                        rooms[rk] = start_state()

                    # ðŸ‘‰ à¹€à¸žà¸´à¹ˆà¸¡à¸šà¸£à¸£à¸—à¸±à¸”à¸™à¸µà¹‰: à¸£à¸µà¹€à¸‹à¹‡à¸•à¸à¸³à¹„à¸£à¸ªà¸°à¸ªà¸¡
                    METRICS["profit_sum"] = 0
                    METRICS["loss_sum"] = 0
                    clear_round_action_guard()

                    msg = "à¹€à¸„à¸¥à¸µà¸¢à¸£à¹Œà¸—à¸±à¹‰à¸‡à¸£à¸°à¸šà¸š (à¸£à¸­à¸š/à¸—à¸¸à¸™) à¸ªà¸³à¹€à¸£à¹‡à¸ˆ âœ“"
                else:
                    # à¹€à¸„à¸¥à¸µà¸¢à¸£à¹Œà¹€à¸‰à¸žà¸²à¸°à¸«à¹‰à¸­à¸‡à¸™à¸µà¹‰ â€” à¸„à¸·à¸™ escrow à¸«à¹‰à¸­à¸‡à¸™à¸µà¹‰
                    stx = rooms.get(key) or start_state()
                    refunded_map = _refund_all_escrow_to_users(stx)
                    total_refund_sum += sum(refunded_map.values())
                    total_refund_users += len(refunded_map)
                    rooms[key] = start_state()
                    clear_round_action_guard(key)
                    msg = "à¹€à¸„à¸¥à¸µà¸¢à¸£à¹Œà¸«à¹‰à¸­à¸‡à¸™à¸µà¹‰ (à¸£à¸­à¸š/à¸—à¸¸à¸™) à¸ªà¸³à¹€à¸£à¹‡à¸ˆ âœ“"

                save_users_persist()

            msg += f"\nà¸„à¸·à¸™à¹€à¸„à¸£à¸”à¸´à¸• {fmt(total_refund_sum)} à¸šà¸²à¸— à¹ƒà¸«à¹‰ {total_refund_users} à¸„à¸™"
            safe_reply(event, TextSendMessage(msg)); return

        # ==== à¹€à¸•à¸´à¸¡/à¸¥à¸šà¸—à¸¸à¸™+à¹€à¸„à¸£à¸”à¸´à¸• à¹à¸šà¸š $+ <cid> <amt> / $- <cid> <amt> ====
        m_add = re.match(r"^\$\+\s*(\d+)\s+(\d+)$", text)
        m_sub = re.match(r"^\$-\s*(\d+)\s+(\d+)$", text)
        if m_add or m_sub:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return

            cid = int((m_add or m_sub).group(1))
            amt = int((m_add or m_sub).group(2))
            with with_users_lock(): # [FIXED] à¹ƒà¸Šà¹‰à¹à¸„à¹ˆ with_users_lock() à¹€à¸žà¸£à¸²à¸° with_rooms_lock() à¸„à¸¥à¸¸à¸¡à¸­à¸¢à¸¹à¹ˆà¹à¸¥à¹‰à¸§
                target = get_user_by_cid(cid)
                if not target:
                    safe_reply(event, TextSendMessage(f"à¹„à¸¡à¹ˆà¸žà¸š ID {cid}")); return
                tuid = target["uid"]
                # [FIXED] à¹€à¸‚à¹‰à¸²à¸–à¸¶à¸‡ rooms[key] à¹„à¸”à¹‰à¹‚à¸”à¸¢à¸•à¸£à¸‡ à¹€à¸žà¸£à¸²à¸° with_rooms_lock() à¸„à¸¥à¸¸à¸¡à¸­à¸¢à¸¹à¹ˆ
                fund_before = rooms[key]["funds"].get(tuid, 0) 
                credit_before = target.get("credit", 0)

                if m_add:
                    target["credit"] = credit_before + amt
                    rooms[key]["funds"][tuid] = fund_before + amt
                    msg = f"âœ…à¹€à¸•à¸´à¸¡à¹€à¸„à¸£à¸”à¸´à¸• {fmt(amt)} à¸šà¸²à¸—  ID : {cid}  {target['name']}  à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­ {fmt(target['credit'])} à¸šà¸²à¸—"
                else:
                    target["credit"] = max(credit_before - amt, 0)
                    rooms[key]["funds"][tuid] = max(fund_before - amt, 0)
                    msg = f"âœ…à¸¥à¸šà¹€à¸„à¸£à¸”à¸´à¸• {fmt(amt)} à¸šà¸²à¸—  ID : {cid}  {target['name']}  à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­ {fmt(target['credit'])} à¸šà¸²à¸—"

                save_users_persist()
            safe_reply(event, TextSendMessage(msg)); return
        



        m_del = R_DEL_USER.match(text)
        if m_del:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™"))
                return

            cid = int(m_del.group(1))

            with with_users_lock():
                target_uid = None
                target = None

                for u in users.values():
                    if u["cid"] == cid:
                        target_uid = u["uid"]
                        target = u
                        break

                if not target:
                    safe_reply(event, TextSendMessage(f"à¹„à¸¡à¹ˆà¸žà¸š ID {cid}"))
                    return

                if has_active_bet(target_uid):
                    safe_reply(event, TextSendMessage("âŒ à¸¥à¸šà¹„à¸¡à¹ˆà¹„à¸”à¹‰: à¸¥à¸¹à¸à¸„à¹‰à¸²à¸¡à¸µà¸šà¸´à¸¥à¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆ"))
                    return

                users.pop(target_uid)
                save_users_persist()

            safe_reply(event, TextSendMessage(f"âœ… à¸¥à¸šà¸¥à¸¹à¸à¸„à¹‰à¸² ID {cid} à¸ªà¸³à¹€à¸£à¹‡à¸ˆ"))
            return        



        # ===== à¹€à¸•à¸´à¸¡à¹€à¸„à¸£à¸”à¸´à¸•à¸£à¸¹à¸›à¹à¸šà¸š @à¸Šà¸·à¹ˆà¸­/à¸ˆà¸³à¸™à¸§à¸™ =====
        if text.startswith("@") and "/" in text:
            msg = process_credit_command(text, uid)
            safe_reply(event, TextSendMessage(msg)); return

        # ==== à¸¥à¸¹à¸à¸„à¹‰à¸²: à¸ªà¸¡à¸±à¸„à¸£/à¸à¸²à¸£à¹Œà¸”/à¸šà¸±à¸à¸Šà¸µ/à¸à¸• ====
        if re.match(r"^add\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)

            # à¹à¸­à¸”à¸¡à¸´à¸™à¸ªà¸¡à¸±à¸„à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸à¹à¸—à¸™à¸¥à¸¹à¸à¸„à¹‰à¸²à¸”à¹‰à¸§à¸¢à¸à¸²à¸£à¹à¸—à¹‡à¸à¸Šà¸·à¹ˆà¸­
            if target_uid and target_uid != uid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™à¸—à¸µà¹ˆà¸ªà¸¡à¸±à¸„à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸à¹à¸—à¸™à¸¥à¸¹à¸à¸„à¹‰à¸²à¹„à¸”à¹‰"))
                    return
                target_user, created = register_customer_by_uid(event.source, target_uid)
                if created:
                    safe_reply(event, TextSendMessage(
                        f"âœ… à¸ªà¸¡à¸±à¸„à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸à¹ƒà¸«à¹‰ {target_user['name']} à¸ªà¸³à¹€à¸£à¹‡à¸ˆ\nðŸŽ« ID: {target_user['cid']}\nà¸žà¸´à¸¡à¸žà¹Œ C @à¸Šà¸·à¹ˆà¸­à¹„à¸¥à¸™à¹Œ à¹€à¸žà¸·à¹ˆà¸­à¸”à¸¹à¸šà¸±à¸•à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸"
                    ))
                else:
                    safe_reply(event, TextSendMessage(
                        f"â„¹ï¸ {target_user['name']} à¸¡à¸µ ID à¸­à¸¢à¸¹à¹ˆà¹à¸¥à¹‰à¸§: {target_user['cid']}"
                    ))
                return

            # à¸ªà¸¡à¸±à¸„à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸à¸”à¹‰à¸§à¸¢à¸•à¸±à¸§à¹€à¸­à¸‡
            if text.lower() == "add":
                target_user, created = register_customer_by_uid(event.source, uid)
                if not created:
                    safe_reply(event, TextSendMessage(f"à¸„à¸¸à¸“à¸¡à¸µ ID à¹à¸¥à¹‰à¸§: {target_user['cid']}"))
                    return
                safe_reply(event, flex_register_success(target_user["cid"])); return

        # à¸¥à¸¹à¸à¸„à¹‰à¸²à¸žà¸´à¸¡à¸žà¹Œ "à¸–à¸­à¸™" à¸—à¸µà¹ˆà¹„à¸«à¸™à¸à¹‡à¹„à¸”à¹‰à¹ƒà¸™à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡ â†’ à¹à¸ªà¸”à¸‡à¸à¸²à¸£à¹Œà¸” C
        if "à¸–à¸­à¸™" in text:
            u = users.get(uid)
            if not u:
                safe_reply(event, TextSendMessage("à¸žà¸´à¸¡à¸žà¹Œ add à¹€à¸žà¸·à¹ˆà¸­à¸£à¸±à¸šà¹„à¸­à¸”à¸µà¸à¹ˆà¸­à¸™"))
                return
            safe_reply(event, flex_customer_card(st, u)); return




        if re.match(r"^c\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)

            # à¹à¸­à¸”à¸¡à¸´à¸™à¸”à¸¹à¸šà¸±à¸•à¸£/ID à¸‚à¸­à¸‡à¸¥à¸¹à¸à¸„à¹‰à¸²à¸—à¸µà¹ˆà¸–à¸¹à¸à¹à¸—à¹‡à¸
            if target_uid and target_uid != uid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™à¸—à¸µà¹ˆà¸”à¸¹à¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¸¥à¸¹à¸à¸„à¹‰à¸²à¸„à¸™à¸­à¸·à¹ˆà¸™à¹„à¸”à¹‰"))
                    return
                u = users.get(target_uid)
                if not u:
                    safe_reply(event, TextSendMessage("à¸¥à¸¹à¸à¸„à¹‰à¸²à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¹„à¸”à¹‰à¸ªà¸¡à¸±à¸„à¸£à¸ªà¸¡à¸²à¸Šà¸´à¸\nà¹ƒà¸«à¹‰à¹à¸­à¸”à¸¡à¸´à¸™à¸žà¸´à¸¡à¸žà¹Œ add @à¸Šà¸·à¹ˆà¸­à¹„à¸¥à¸™à¹Œ à¸à¹ˆà¸­à¸™"))
                    return
                safe_reply(event, flex_customer_card(st, u)); return

            # à¸¥à¸¹à¸à¸„à¹‰à¸²à¸”à¸¹à¸šà¸±à¸•à¸£à¸‚à¸­à¸‡à¸•à¸±à¸§à¹€à¸­à¸‡
            if text.lower() == "c":
                u = users.get(uid)
                if not u:
                    safe_reply(event, TextSendMessage("à¸žà¸´à¸¡à¸žà¹Œ add à¹€à¸žà¸·à¹ˆà¸­à¸£à¸±à¸šà¹„à¸­à¸”à¸µà¸à¹ˆà¸­à¸™"))
                    return
                safe_reply(event, flex_customer_card(st, u)); return

        if text.strip().lower() in ("à¸šà¸Š", "à¸šà¸±à¸à¸Šà¸µ", "à¹€à¸¥à¸‚à¸šà¸±à¸à¸Šà¸µ"):
            # à¸ªà¹ˆà¸‡ "à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸­à¸¢à¹ˆà¸²à¸‡à¹€à¸”à¸µà¸¢à¸§" à¹„à¸¡à¹ˆà¸ªà¹ˆà¸‡à¸›à¸¸à¹ˆà¸¡ Flex
            safe_reply(event, text_bank())
            return

        if text == "à¸à¸•":
            safe_reply(event, TextSendMessage(rules_text())); return

        # ==== à¸›à¸£à¸°à¸à¸²à¸¨à¸£à¸²à¸„à¸²à¹à¸šà¸š "à¸ªà¹ˆà¸‡à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸­à¸¢à¹ˆà¸²à¸‡à¹€à¸”à¸µà¸¢à¸§" (à¹„à¸¡à¹ˆà¹€à¸›à¸´à¸”à¸£à¸­à¸š) ====
        # ==== à¸›à¸£à¸°à¸à¸²à¸¨à¸£à¸²à¸„à¸²à¹à¸šà¸š "à¸ªà¹ˆà¸‡à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸­à¸¢à¹ˆà¸²à¸‡à¹€à¸”à¸µà¸¢à¸§" (à¹„à¸¡à¹ˆà¹€à¸›à¸´à¸”à¸£à¸­à¸š) ====
        m_announce = R_ANN.match(text)

        if m_announce and not re.match(r"^\s*o\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸›à¸£à¸°à¸à¸²à¸¨à¸£à¸²à¸„à¸²à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™"))
                return

            camp   = m_announce.group(1).strip()
            hi_min = int(m_announce.group(2)); hi_max = int(m_announce.group(3))
            lo_min = int(m_announce.group(4)); lo_max = int(m_announce.group(5))

            safe_reply(event, flex_open_with_prices(
                st["pairNo"], camp, hi_min, hi_max, lo_min, lo_max
            )); return

        # ==== à¹€à¸›à¸´à¸”à¸£à¸­à¸š (O) ====
        if re.match(r"^\s*o\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return

            if st["phase"] != "NONE":
                phase_th = "à¹€à¸›à¸´à¸”à¸­à¸¢à¸¹à¹ˆ" if st["phase"] == "OPEN" else "à¸žà¸±à¸à¸£à¸­à¸šà¸­à¸¢à¸¹à¹ˆ"
                safe_reply(
                    event,
                    TextSendMessage(
                        f"âŒ à¹€à¸›à¸´à¸”à¸£à¸­à¸šà¹ƒà¸«à¸¡à¹ˆà¹„à¸¡à¹ˆà¹„à¸”à¹‰: à¸¢à¸±à¸‡à¸¡à¸µà¸£à¸­à¸šà¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆ ({phase_th})\n"
                        f"à¸‚à¸±à¹‰à¸™à¸•à¸­à¸™à¸—à¸µà¹ˆà¸–à¸¹à¸à¸•à¹‰à¸­à¸‡: à¸à¸” E à¹€à¸žà¸·à¹ˆà¸­à¸žà¸±à¸ â†’ à¸žà¸´à¸¡à¸žà¹Œ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> â†’ /y à¹€à¸žà¸·à¹ˆà¸­à¸¢à¸·à¸™à¸¢à¸±à¸™à¸œà¸¥\n"
                        f"à¹€à¸¡à¸·à¹ˆà¸­à¸ªà¸£à¸¸à¸›à¸£à¸­à¸šà¹€à¸ªà¸£à¹‡à¸ˆà¹à¸¥à¹‰à¸§ à¸ˆà¸¶à¸‡à¸„à¹ˆà¸­à¸¢à¹€à¸›à¸´à¸”à¸£à¸­à¸šà¹ƒà¸«à¸¡à¹ˆà¹„à¸”à¹‰"
                    )
                ); return

            m = R_O_ANN.match(text)
            if m:
                camp = m.group(1).strip()
                hi_min, hi_max = int(m.group(2)), int(m.group(3))
                lo_min, lo_max = int(m.group(4)), int(m.group(5))

                st["pairNo"] += 1
                st["totals"] = {"HI": 0, "LO": 0}
                st["bet_index"] = {}
                st["pendingCode"] = None
                st["escrow"] = {}
                st["settling"] = False
                st["phase"] = "OPEN"
                st["price"] = {"camp": camp, "HI": (hi_min, hi_max), "LO": (lo_min, lo_max)}

                safe_reply(event, flex_open_with_prices(
                    st["pairNo"], camp, hi_min, hi_max, lo_min, lo_max
                )); return
            else:
                note = (re.match(r"^\s*o\b\s*(.*)$", text, re.IGNORECASE).group(1) or "").strip()

                st["pairNo"] += 1
                st["totals"] = {"HI": 0, "LO": 0}
                st["bet_index"] = {}
                st["pendingCode"] = None
                st["escrow"] = {}
                st["settling"] = False
                st["phase"] = "OPEN"
                st["note"] = note or st.get("note")

                safe_reply(event, flex_open(st["pairNo"], st.get("note"))); return

        t = text.upper()
        if t == "E":
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™"))
                return
            if st["phase"] != "OPEN":
                safe_reply(event, TextSendMessage("à¹„à¸¡à¹ˆà¸¡à¸µà¸£à¸­à¸šà¸—à¸µà¹ˆà¹€à¸›à¸´à¸”à¸­à¸¢à¸¹à¹ˆ"))
                return

            claimed, old_action = claim_round_action("close", key, st["pairNo"], uid)
            if not claimed:
                st["phase"] = "PAUSED"
                st["last_closed_pairNo"] = st["pairNo"]
                safe_reply(event, TextSendMessage(
                    f"âš ï¸ à¸£à¸­à¸š {st['pairNo']} à¸›à¸´à¸”à¸£à¸±à¸šà¸šà¸´à¸¥à¹„à¸›à¹à¸¥à¹‰à¸§ à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¸›à¸´à¸”à¸‹à¹‰à¸³"
                ))
                return

            st["phase"] = "PAUSED"
            st["last_closed_pairNo"] = st["pairNo"]
            camp = current_camp(st)

            # à¸ªà¹ˆà¸‡ 2 à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡: (1) à¸à¸²à¸£à¹Œà¸”à¸žà¸±à¸à¸£à¸­à¸š (2) à¸ªà¸£à¸¸à¸›à¸šà¸´à¸¥
            try:
                safe_reply(event, [
                    flex_pause_notice(st["pairNo"], camp),
                    flex_summary(st, event)
                ])
            except Exception as e:
                # à¸à¸±à¸™à¸•à¸ à¸–à¹‰à¸²à¸¡à¸µà¸›à¸±à¸à¸«à¸² Flex à¸ˆà¸°à¸¢à¸±à¸‡à¸•à¸­à¸šà¹€à¸›à¹‡à¸™à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¹„à¸”à¹‰
                safe_reply(event, TextSendMessage(f"à¸žà¸±à¸à¸£à¸­à¸šà¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§ #{st['pairNo']} â€” à¸„à¹ˆà¸²à¸¢ {camp}"))
            return

        
        if t in ("R", "RESUME"):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); 
                return
            if st["phase"] != "PAUSED":
                safe_reply(event, TextSendMessage("à¹„à¸¡à¹ˆà¸¡à¸µà¸£à¸­à¸šà¸—à¸µà¹ˆà¸žà¸±à¸à¸­à¸¢à¸¹à¹ˆ")); return
            release_round_action("close", key, st["pairNo"])
            st["phase"] = "OPEN"
            camp = current_camp(st)
            safe_reply(event, flex_resume(st["pairNo"], camp)); return




        

        
            # ==== à¸›à¸´à¸”à¸£à¸­à¸š (à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¹„à¸—à¸¢: à¸›à¸´à¸”à¸£à¸­à¸š / à¸«à¸¢à¸¸à¸”à¹à¸—à¸‡ / à¸›à¸´à¸”) ====
        if R_CLOSE_TH.match(text.strip()):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return

            # à¸ªà¸³à¸„à¸±à¸: à¸›à¸´à¸”à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¸•à¸­à¸™ OPEN à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™
            # à¸–à¹‰à¸² PAUSED à¸­à¸¢à¸¹à¹ˆà¹à¸¥à¹‰à¸§ à¸«à¹‰à¸²à¸¡à¸ªà¹ˆà¸‡à¸à¸²à¸£à¹Œà¸”à¸›à¸´à¸”/à¸ªà¸£à¸¸à¸›à¸‹à¹‰à¸³
            if st["phase"] != "OPEN":
                if st["phase"] == "PAUSED":
                    safe_reply(event, TextSendMessage(
                        f"âš ï¸ à¸£à¸­à¸š {st['pairNo']} à¸›à¸´à¸”à¸£à¸±à¸šà¸šà¸´à¸¥à¹„à¸›à¹à¸¥à¹‰à¸§ à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¸›à¸´à¸”à¸‹à¹‰à¸³\n"
                        f"à¸‚à¸±à¹‰à¸™à¸•à¸­à¸™à¸–à¸±à¸”à¹„à¸›: à¸žà¸´à¸¡à¸žà¹Œ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> à¹à¸¥à¹‰à¸§à¸à¸”à¸¢à¸·à¸™à¸¢à¸±à¸™ /y"
                    )); return
                if st["phase"] == "SETTLING" or st.get("settling"):
                    safe_reply(event, TextSendMessage("â³ à¸£à¸°à¸šà¸šà¸à¸³à¸¥à¸±à¸‡à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸­à¸¢à¸¹à¹ˆ à¸à¸£à¸¸à¸“à¸²à¸£à¸­à¸ªà¸±à¸à¸„à¸£à¸¹à¹ˆ")); return

                safe_reply(event, TextSendMessage("à¹„à¸¡à¹ˆà¸¡à¸µà¸£à¸­à¸šà¸—à¸µà¹ˆà¹€à¸›à¸´à¸”à¸­à¸¢à¸¹à¹ˆ")); return

            claimed, old_action = claim_round_action("close", key, st["pairNo"], uid)
            if not claimed:
                st["phase"] = "PAUSED"
                st["last_closed_pairNo"] = st["pairNo"]
                safe_reply(event, TextSendMessage(
                    f"âš ï¸ à¸£à¸­à¸š {st['pairNo']} à¸›à¸´à¸”à¸£à¸±à¸šà¸šà¸´à¸¥à¹„à¸›à¹à¸¥à¹‰à¸§ à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¸›à¸´à¸”à¸‹à¹‰à¸³\n"
                    f"à¸‚à¸±à¹‰à¸™à¸•à¸­à¸™à¸–à¸±à¸”à¹„à¸›: à¸žà¸´à¸¡à¸žà¹Œ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> à¹à¸¥à¹‰à¸§à¸à¸”à¸¢à¸·à¸™à¸¢à¸±à¸™ /y"
                )); return

            # à¹€à¸›à¸¥à¸µà¹ˆà¸¢à¸™à¸ªà¸–à¸²à¸™à¸°à¹€à¸›à¹‡à¸™à¸žà¸±à¸à¸£à¸­à¸šà¸—à¸±à¸™à¸—à¸µ à¸à¹ˆà¸­à¸™à¸ªà¹ˆà¸‡à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡ à¹€à¸žà¸·à¹ˆà¸­à¸à¸±à¸™à¹à¸­à¸”à¸¡à¸´à¸™à¸­à¸µà¸à¸„à¸™à¸à¸”à¸‹à¹‰à¸­à¸™
            st["phase"] = "PAUSED"
            st["last_closed_pairNo"] = st["pairNo"]

            # à¸ªà¹ˆà¸‡à¸à¸²à¸£à¹Œà¸”à¹à¸ˆà¹‰à¸‡à¸«à¸¢à¸¸à¸”à¹à¸—à¸‡ + à¸ªà¸£à¸¸à¸›à¸šà¸´à¸¥à¸£à¸­à¸šà¸™à¸µà¹‰
            safe_reply(event, [
                flex_close_notice(st["pairNo"]),
                flex_summary(st, event)
            ]); return


        # ==== à¸•à¸±à¹‰à¸‡à¸œà¸¥ s... ====
        sm = re.match(r"^[sS]\s*(.+)$", text)
        if sm:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return
            if st["phase"] != "PAUSED":
                safe_reply(event, TextSendMessage("âŒ à¸•à¹‰à¸­à¸‡à¸à¸” E (à¸žà¸±à¸à¸£à¸­à¸š) à¸à¹ˆà¸­à¸™à¸ˆà¸¶à¸‡à¸ˆà¸°à¸•à¸±à¹‰à¸‡à¸œà¸¥à¹„à¸”à¹‰")); return
            st["pendingCode"] = normalize_result_code(sm.group(1))
            safe_reply(event, flex_result_preview(st["pendingCode"], st["pairNo"])); return

        # ==== à¸¢à¸·à¸™à¸¢à¸±à¸™à¸œà¸¥: T/ à¸«à¸£à¸·à¸­ /y ====
        if R_YCONFIRM.match(text.strip()):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return

            # à¸à¸±à¸™à¹à¸­à¸”à¸¡à¸´à¸™à¸à¸” /y à¸‹à¹‰à¸­à¸™ à¸«à¸£à¸·à¸­ LINE retry à¸£à¸°à¸«à¸§à¹ˆà¸²à¸‡à¸à¸³à¸¥à¸±à¸‡à¸„à¸³à¸™à¸§à¸“à¹€à¸„à¸£à¸”à¸´à¸•
            if st.get("settling") or st["phase"] == "SETTLING":
                safe_reply(event, TextSendMessage("â³ à¸£à¸°à¸šà¸šà¸à¸³à¸¥à¸±à¸‡à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸­à¸¢à¸¹à¹ˆ à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸¢à¸·à¸™à¸¢à¸±à¸™à¸‹à¹‰à¸³à¸–à¸¹à¸à¸¢à¸à¹€à¸¥à¸´à¸")); return

            if st["phase"] != "PAUSED":
                if st.get("last_settled_pairNo") == st.get("pairNo"):
                    safe_reply(event, TextSendMessage(f"âš ï¸ à¸£à¸­à¸š {st['pairNo']} à¸ªà¸£à¸¸à¸›à¸œà¸¥à¹„à¸›à¹à¸¥à¹‰à¸§ à¹„à¸¡à¹ˆà¸ªà¸²à¸¡à¸²à¸£à¸–à¸¢à¸·à¸™à¸¢à¸±à¸™à¸‹à¹‰à¸³à¹„à¸”à¹‰")); return
                safe_reply(event, TextSendMessage("âŒ à¸•à¹‰à¸­à¸‡à¸à¸” E (à¸žà¸±à¸à¸£à¸­à¸š) à¸à¹ˆà¸­à¸™à¸ˆà¸¶à¸‡à¸ˆà¸°à¸ªà¸²à¸¡à¸²à¸£à¸–à¸ªà¸£à¸¸à¸›à¸œà¸¥à¹„à¸”à¹‰")); return

            if not st.get("pendingCode"):
                safe_reply(event, TextSendMessage(
                    f"âŒ à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¹„à¸”à¹‰à¸•à¸±à¹‰à¸‡à¸œà¸¥à¸£à¸­à¸š {st['pairNo']}\n"
                    f"à¸à¸£à¸¸à¸“à¸²à¸žà¸´à¸¡à¸žà¹Œ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> à¸à¹ˆà¸­à¸™ à¹à¸¥à¹‰à¸§à¸„à¹ˆà¸­à¸¢à¸à¸”à¸¢à¸·à¸™à¸¢à¸±à¸™ /y"
                )); return

            code = normalize_result_code(st["pendingCode"])
            if code not in RESULT_DEFS:
                safe_reply(event, TextSendMessage("âŒ à¹„à¸¡à¹ˆà¸ªà¸²à¸¡à¸²à¸£à¸–à¸¢à¸·à¸™à¸¢à¸±à¸™à¸œà¸¥à¹„à¸”à¹‰: à¹‚à¸„à¹‰à¸”à¸œà¸¥à¹„à¸¡à¹ˆà¸–à¸¹à¸à¸•à¹‰à¸­à¸‡")); return

            claimed, old_action = claim_round_action("settle", key, st["pairNo"], uid)
            if not claimed:
                st["phase"] = "NONE"
                st["settling"] = False
                safe_reply(event, TextSendMessage(
                    f"âš ï¸ à¸£à¸­à¸š {st['pairNo']} à¸à¸³à¸¥à¸±à¸‡à¸–à¸¹à¸à¸ªà¸£à¸¸à¸›à¸œà¸¥ à¸«à¸£à¸·à¸­à¸ªà¸£à¸¸à¸›à¸œà¸¥à¹„à¸›à¹à¸¥à¹‰à¸§ à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸¢à¸·à¸™à¸¢à¸±à¸™à¸‹à¹‰à¸³à¸–à¸¹à¸à¸¢à¸à¹€à¸¥à¸´à¸"
                )); return

            # à¸¥à¹‡à¸­à¸à¸ªà¸–à¸²à¸™à¸°à¸—à¸±à¸™à¸—à¸µ à¸à¹ˆà¸­à¸™à¹€à¸£à¸´à¹ˆà¸¡ backup/à¸„à¸³à¸™à¸§à¸“/à¸„à¸·à¸™à¹€à¸„à¸£à¸”à¸´à¸•
            st["phase"] = "SETTLING"
            st["settling"] = True


            # ================= [à¹€à¸£à¸´à¹ˆà¸¡à¸ªà¹ˆà¸§à¸™à¸—à¸µà¹ˆà¹€à¸žà¸´à¹ˆà¸¡] =================
            # 1. à¸šà¸±à¸™à¸—à¸¶à¸à¸›à¸£à¸°à¸§à¸±à¸•à¸´à¸¥à¸‡ State
            current_camp_name = current_camp(st)
            if "score_history" not in st: 
                st["score_history"] = []
                
            st["score_history"].append({
                "round": st["pairNo"],
                "camp": current_camp_name,
                "code": code
            })

            # === [à¹€à¸žà¸´à¹ˆà¸¡à¹ƒà¸«à¸¡à¹ˆ] à¸šà¸±à¸™à¸—à¸¶à¸ snapshot à¹€à¸„à¸£à¸”à¸´à¸• + à¸ªà¸–à¸²à¸™à¸°à¸«à¹‰à¸­à¸‡ à¸à¹ˆà¸­à¸™à¸ªà¸£à¸¸à¸›à¸œà¸¥ ===
            try:
                backup_path = os.path.join(DATA_DIR, f"backup_round_{st['pairNo']}.json")
                with with_users_lock(): # [FIXED] à¹ƒà¸Šà¹‰à¹à¸„à¹ˆ with_users_lock()
                    snapshot = {
                        "round": st["pairNo"],
                        "users": users,
                        "room_state": st.copy(),   # âœ… st à¸­à¸¢à¸¹à¹ˆà¹ƒà¸™ with_rooms_lock() à¸­à¸¢à¸¹à¹ˆà¹à¸¥à¹‰à¸§
                        "metrics": METRICS.copy(), 
                    }
                    _atomic_write_json(backup_path, snapshot)

                # à¸•à¸±à¹‰à¸‡à¹€à¸§à¸¥à¸²à¸¥à¸š backup_round à¹„à¸Ÿà¸¥à¹Œà¸™à¸µà¹‰à¹€à¸¡à¸·à¹ˆà¸­à¸„à¸£à¸š 1 à¸§à¸±à¸™ à¹‚à¸”à¸¢à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¹€à¸Šà¹‡à¸„à¸—à¸¸à¸à¸Šà¸±à¹ˆà¸§à¹‚à¸¡à¸‡
                schedule_backup_round_delete(backup_path)

                app.logger.info(f"[Backup] à¸šà¸±à¸™à¸—à¸¶à¸à¹€à¸„à¸£à¸”à¸´à¸•à¸à¹ˆà¸­à¸™à¸ªà¸£à¸¸à¸›à¸œà¸¥ à¸£à¸­à¸š {st['pairNo']} à¸ªà¸³à¹€à¸£à¹‡à¸ˆ")
            except Exception as e:
                app.logger.warning(f"[Backup] à¹„à¸¡à¹ˆà¸ªà¸²à¸¡à¸²à¸£à¸–à¸šà¸±à¸™à¸—à¸¶à¸ snapshot à¸£à¸­à¸š {st['pairNo']}: {e}")
            # === [à¸ˆà¸šà¸ªà¹ˆà¸§à¸™à¹€à¸žà¸´à¹ˆà¸¡à¹ƒà¸«à¸¡à¹ˆ] ===


            # à¸„à¸³à¸™à¸§à¸“à¸¢à¸­à¸” à¹à¸¥à¸°à¸„à¸·à¸™à¹€à¸„à¸£à¸”à¸´à¸•à¹ƒà¸«à¹‰à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™
            sum_stake = sum(b["amount"] for b in st["bet_index"].values())
            rows, footer = settle_by_code(st, code)

            with with_users_lock():
                for r in rows:
                    u = users.get(r["uid"])
                    if u:
                        u["credit"] = max(u.get("credit", 0) + r["payout"], 0)
                save_users_persist()

            # à¸¥à¹‰à¸²à¸‡ state à¸«à¹‰à¸­à¸‡ à¸«à¸¥à¸±à¸‡à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸ªà¸³à¹€à¸£à¹‡à¸ˆ
            st["last_settled_pairNo"] = st["pairNo"]
            st["settling"] = False
            st["phase"] = "NONE"
            st["pendingCode"] = None
            st["bet_index"].clear()
            st["totals"] = {"HI": 0, "LO": 0}
            st["escrow"].clear()

            # à¸–à¹‰à¸²à¸£à¸­à¸šà¸™à¸µà¹‰à¹€à¸„à¸¢à¸–à¸¹à¸à¸¢à¹‰à¸­à¸™à¹à¸¥à¹‰à¸§ à¹à¸¥à¸°à¸•à¸­à¸™à¸™à¸µà¹‰à¸­à¸­à¸à¸œà¸¥à¹ƒà¸«à¸¡à¹ˆà¸ªà¸³à¹€à¸£à¹‡à¸ˆà¹à¸¥à¹‰à¸§
            # à¹ƒà¸«à¹‰à¸›à¸¥à¸”à¸¥à¹‡à¸­à¸ rollback/pending snapshot à¹€à¸žà¸·à¹ˆà¸­à¹ƒà¸«à¹‰à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸­à¸šà¸™à¸µà¹‰à¹„à¸”à¹‰à¸­à¸µà¸à¸„à¸£à¸±à¹‰à¸‡à¹€à¸‰à¸žà¸²à¸°à¸«à¸¥à¸±à¸‡à¸­à¸­à¸à¸œà¸¥à¹ƒà¸«à¸¡à¹ˆà¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™
            release_round_action("rollback", key, st["pairNo"])
            clear_pending_rollback_snapshot(key)

            sum_payout = sum(r["payout"] for r in rows)
            profit = sum_stake - sum_payout
            if profit >= 0:
                METRICS["profit_sum"] += profit
            else:
                METRICS["loss_sum"] += (-profit)

            accum_now = {"profit_sum": METRICS["profit_sum"], "loss_sum": METRICS["loss_sum"], "net": net_profit()}
            balance_map = {r["uid"]: users.get(r["uid"], {}).get("credit", 0) for r in rows}
            # 1. à¸”à¸¶à¸‡à¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢à¸¡à¸²à¸£à¸­à¹„à¸§à¹‰
            current_camp_name = current_camp(st)

            # [FREE] à¹€à¸à¹‡à¸šà¸ªà¸£à¸¸à¸›à¸¥à¹ˆà¸²à¸ªà¸¸à¸”à¹„à¸§à¹‰à¹ƒà¸«à¹‰à¸«à¸¥à¸±à¸‡à¸šà¹‰à¸²à¸™à¹€à¸£à¸µà¸¢à¸à¸”à¸¹à¹„à¸”à¹‰ (à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡ push = à¸›à¸£à¸°à¸«à¸¢à¸±à¸”à¹‚à¸„à¸§à¸•à¹‰à¸²)
            try:
                rows_payload = []
                for r in rows:
                    rr = dict(r)
                    rr["name"] = users.get(r.get("uid"), {}).get("name")
                    rows_payload.append(rr)

                save_last_settle({
                    "round": st["pairNo"],
                    "camp_name": current_camp_name,
                    "code": code,
                    "profit": profit,
                    "accum": accum_now,
                    "rows": rows_payload,
                    "footer": footer,
                    "ts": _now(),
                    "ts_iso": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                })
            except Exception:
                app.logger.exception("build/save last_settle failed")

            # 2. à¸ªà¹ˆà¸‡à¹ƒà¸«à¹‰à¸«à¹‰à¸­à¸‡à¸¥à¸¹à¸à¸„à¹‰à¸² (à¹à¸ªà¸”à¸‡à¸Šà¸·à¹ˆà¸­à¸„à¹ˆà¸²à¸¢à¸”à¹‰à¸§à¸¢)
            safe_reply(event, [
                flex_settle(st["pairNo"], rows, footer,
                            show_profit=False,
                            balance_map=balance_map,
                            camp_name=current_camp_name),
                flex_scoreboard(st["score_history"])
            ]);

            # 3) à¸«à¸¥à¸±à¸‡à¸šà¹‰à¸²à¸™à¹à¸šà¸šà¸Ÿà¸£à¸µ (à¹à¸™à¸°à¸™à¸³): à¹ƒà¸«à¹‰à¸žà¸´à¸¡à¸žà¹Œ "à¸à¸³à¹„à¸£à¸¥à¹ˆà¸²à¸ªà¸¸à¸”" à¹ƒà¸™à¸à¸¥à¸¸à¹ˆà¸¡à¸«à¸¥à¸±à¸‡à¸šà¹‰à¸²à¸™à¹€à¸žà¸·à¹ˆà¸­à¸”à¸¶à¸‡à¸œà¸¥à¸¥à¹ˆà¸²à¸ªà¸¸à¸”
            #    * à¸–à¹‰à¸²à¸ˆà¸³à¹€à¸›à¹‡à¸™à¸•à¹‰à¸­à¸‡à¸ªà¹ˆà¸‡à¸­à¸±à¸•à¹‚à¸™à¸¡à¸±à¸•à¸´à¸ˆà¸£à¸´à¸‡ à¹† à¹ƒà¸«à¹‰à¸•à¸±à¹‰à¸‡ env: BACKOFFICE_PUSH_ENABLED=1
            if os.getenv("BACKOFFICE_PUSH_ENABLED", "0") == "1":
                p = load_last_settle()
                if p:
                    msg = TextSendMessage(settle_payload_to_text(p))
                    # à¸ªà¹ˆà¸‡à¹à¸„à¹ˆ 1 à¸à¸¥à¸¸à¹ˆà¸¡à¹à¸£à¸ à¹€à¸žà¸·à¹ˆà¸­à¸¥à¸”à¹‚à¸„à¸§à¸•à¹‰à¸² (à¸›à¸£à¸±à¸šà¹„à¸”à¹‰à¸–à¹‰à¸²à¸•à¹‰à¸­à¸‡à¸à¸²à¸£)
                    bo_targets = BACKOFFICE_GROUP_IDS[:1]
                    for gid_to in bo_targets:
                        safe_push(gid_to, msg, label="backoffice_text")

            return
        # ==== à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™à¸œà¸¥ (Cancel Rollback) ====
        m_cancel_rollback = re.match(r"^(?:à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™|cancel\s+rollback|cancelrollback)\s*(\d+)$", text.strip(), re.IGNORECASE)
        if m_cancel_rollback:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return

            round_no = int(m_cancel_rollback.group(1))
            active_rb = get_active_round_action("rollback", key)
            if not active_rb:
                safe_reply(event, TextSendMessage(
                    f"â„¹ï¸ à¸•à¸­à¸™à¸™à¸µà¹‰à¹„à¸¡à¹ˆà¸¡à¸µà¸£à¸²à¸¢à¸à¸²à¸£à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆ à¸ˆà¸¶à¸‡à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™ {round_no}"
                )); return

            active_round = int(active_rb.get("pair_no") or 0)
            if active_round != round_no:
                safe_reply(event, TextSendMessage(
                    f"âš ï¸ à¸•à¸­à¸™à¸™à¸µà¹‰à¸£à¸²à¸¢à¸à¸²à¸£à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸—à¸µà¹ˆà¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆà¸„à¸·à¸­à¸£à¸­à¸š {active_round}\n"
                    f"à¸–à¹‰à¸²à¸ˆà¸°à¸¢à¸à¹€à¸¥à¸´à¸ à¹ƒà¸«à¹‰à¸žà¸´à¸¡à¸žà¹Œ: à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™ {active_round}\n"
                    f"à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸ªà¸²à¸¡à¸²à¸£à¸–à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™ {round_no} à¹„à¸”à¹‰"
                )); return

            snap = load_pending_rollback_snapshot(key)
            if not snap or int(snap.get("round_no") or 0) != round_no:
                safe_reply(event, TextSendMessage(
                    f"âŒ à¹„à¸¡à¹ˆà¸žà¸šà¸ªà¸–à¸²à¸™à¸°à¸à¹ˆà¸­à¸™à¸¢à¹‰à¸­à¸™à¸‚à¸­à¸‡à¸£à¸­à¸š {round_no}\n"
                    f"à¹€à¸žà¸·à¹ˆà¸­à¸›à¹‰à¸­à¸‡à¸à¸±à¸™à¹€à¸„à¸£à¸”à¸´à¸•à¹€à¸žà¸µà¹‰à¸¢à¸™ à¸à¸£à¸¸à¸“à¸²à¸•à¸±à¹‰à¸‡à¸œà¸¥à¸£à¸­à¸š {round_no} à¹ƒà¸«à¸¡à¹ˆà¸”à¹‰à¸§à¸¢ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> à¹à¸¥à¹‰à¸§à¸à¸”à¸¢à¸·à¸™à¸¢à¸±à¸™ /y à¹ƒà¸«à¹‰à¹€à¸ªà¸£à¹‡à¸ˆà¸à¹ˆà¸­à¸™"
                )); return

            try:
                # à¸„à¸·à¸™à¸ªà¸–à¸²à¸™à¸°à¸à¸¥à¸±à¸šà¹„à¸›à¸à¹ˆà¸­à¸™à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸¢à¹‰à¸­à¸™à¸œà¸¥ à¹€à¸«à¸¡à¸·à¸­à¸™à¸¢à¸à¹€à¸¥à¸´à¸à¸à¸²à¸£à¸¢à¹‰à¸­à¸™à¸ˆà¸£à¸´à¸‡ à¹†
                with with_users_lock():
                    users.clear()
                    users.update(snap.get("users") or {})
                save_users_persist()

                st.clear()
                st.update(snap.get("room_state") or start_state())

                if "metrics" in snap:
                    METRICS.clear()
                    METRICS.update(snap["metrics"])

                if snap.get("last_settle") is not None:
                    save_last_settle(snap.get("last_settle"))

                release_round_action("rollback", key, round_no)
                # à¸à¸¥à¸±à¸šà¸ªà¸–à¸²à¸™à¸°à¹€à¸›à¹‡à¸™à¸­à¸­à¸à¸œà¸¥à¹à¸¥à¹‰à¸§ à¸ˆà¸¶à¸‡à¸•à¹‰à¸­à¸‡à¸¥à¹‡à¸­à¸ settle à¸£à¸­à¸šà¸™à¸µà¹‰à¹„à¸§à¹‰à¹€à¸«à¸¡à¸·à¸­à¸™à¹€à¸”à¸´à¸¡
                if not has_round_action("settle", key, round_no):
                    claim_round_action("settle", key, round_no, uid)
                clear_pending_rollback_snapshot(key)

                safe_reply(event, TextSendMessage(
                    f"âœ… à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸­à¸š {round_no} à¸ªà¸³à¹€à¸£à¹‡à¸ˆà¹à¸¥à¹‰à¸§\n"
                    f"à¸£à¸°à¸šà¸šà¸„à¸·à¸™à¸ªà¸–à¸²à¸™à¸°à¸à¸¥à¸±à¸šà¹„à¸›à¸à¹ˆà¸­à¸™à¸¢à¹‰à¸­à¸™à¸œà¸¥à¹€à¸£à¸µà¸¢à¸šà¸£à¹‰à¸­à¸¢\n"
                    f"à¸•à¸­à¸™à¸™à¸µà¹‰à¸ªà¸²à¸¡à¸²à¸£à¸–à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸­à¸šà¸­à¸·à¹ˆà¸™à¹„à¸”à¹‰à¹à¸¥à¹‰à¸§"
                )); return
            except Exception:
                app.logger.exception("cancel rollback failed")
                safe_reply(event, TextSendMessage(
                    f"âŒ à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸­à¸š {round_no} à¹„à¸¡à¹ˆà¸ªà¸³à¹€à¸£à¹‡à¸ˆ\n"
                    f"à¹€à¸žà¸·à¹ˆà¸­à¸„à¸§à¸²à¸¡à¸›à¸¥à¸­à¸”à¸ à¸±à¸¢ à¸à¸£à¸¸à¸“à¸²à¸•à¸±à¹‰à¸‡à¸œà¸¥à¸£à¸­à¸š {round_no} à¹ƒà¸«à¸¡à¹ˆà¸”à¹‰à¸§à¸¢ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> à¹à¸¥à¹‰à¸§ /y à¹ƒà¸«à¹‰à¸ˆà¸šà¸à¹ˆà¸­à¸™"
                )); return

        # ==== à¸¢à¹‰à¸­à¸™à¸œà¸¥ (Rollback) ====
        m_rollback = re.match(r"^(?:à¸¢à¹‰à¸­à¸™à¸œà¸¥|rollback)\s*(\d+)$", text.strip(), re.IGNORECASE)
        if m_rollback:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return

            round_no = int(m_rollback.group(1))

            # à¸«à¹‰à¸²à¸¡à¸¢à¹‰à¸­à¸™à¸•à¸­à¸™à¸£à¸°à¸šà¸šà¸à¸³à¸¥à¸±à¸‡à¸ªà¸£à¸¸à¸›à¸œà¸¥ à¹€à¸žà¸·à¹ˆà¸­à¸à¸±à¸™à¹€à¸„à¸£à¸”à¸´à¸•/à¹„à¸Ÿà¸¥à¹Œ snapshot à¸Šà¸™à¸à¸±à¸™
            if st.get("settling") or st.get("phase") == "SETTLING":
                safe_reply(event, TextSendMessage(
                    f"â³ à¸£à¸°à¸šà¸šà¸à¸³à¸¥à¸±à¸‡à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸£à¸­à¸š {st.get('pairNo')} à¸­à¸¢à¸¹à¹ˆ à¸«à¹‰à¸²à¸¡à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸°à¸«à¸§à¹ˆà¸²à¸‡à¸™à¸µà¹‰"
                )); return

            # à¸¥à¹‡à¸­à¸ global à¸•à¹ˆà¸­à¸«à¹‰à¸­à¸‡: à¸–à¹‰à¸²à¸¢à¹‰à¸­à¸™à¸£à¸­à¸šà¹ƒà¸”à¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆ à¸«à¹‰à¸²à¸¡à¸¢à¹‰à¸­à¸™à¸£à¸­à¸šà¸­à¸·à¹ˆà¸™à¸ˆà¸™à¸à¸§à¹ˆà¸²à¸ˆà¸°à¸­à¸­à¸à¸œà¸¥à¹ƒà¸«à¸¡à¹ˆà¸«à¸£à¸·à¸­à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™
            active_rb = get_active_round_action("rollback", key)
            if active_rb:
                active_round = int(active_rb.get("pair_no") or 0)
                if active_round == round_no:
                    safe_reply(event, TextSendMessage(
                        f"âš ï¸ à¸£à¸­à¸š {round_no} à¸–à¸¹à¸à¸¢à¹‰à¸­à¸™à¸œà¸¥à¹„à¸›à¹à¸¥à¹‰à¸§\n"
                        f"à¸•à¹‰à¸­à¸‡à¸•à¸±à¹‰à¸‡à¸œà¸¥à¸£à¸­à¸š {round_no} à¹ƒà¸«à¸¡à¹ˆà¸”à¹‰à¸§à¸¢ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> à¹à¸¥à¹‰à¸§à¸à¸”à¸¢à¸·à¸™à¸¢à¸±à¸™ /y à¹ƒà¸«à¹‰à¹€à¸ªà¸£à¹‡à¸ˆà¸à¹ˆà¸­à¸™\n"
                        f"à¸«à¸£à¸·à¸­à¸žà¸´à¸¡à¸žà¹Œ: à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™ {round_no}\n"
                        f"à¸«à¹‰à¸²à¸¡à¸žà¸´à¸¡à¸žà¹Œà¸¢à¹‰à¸­à¸™à¸œà¸¥à¸‹à¹‰à¸³"
                    )); return
                else:
                    safe_reply(event, TextSendMessage(
                        f"âš ï¸ à¸•à¸­à¸™à¸™à¸µà¹‰à¸¡à¸µà¸£à¸²à¸¢à¸à¸²à¸£à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸­à¸š {active_round} à¸„à¹‰à¸²à¸‡à¸­à¸¢à¸¹à¹ˆ\n"
                        f"à¸•à¹‰à¸­à¸‡à¸ˆà¸±à¸”à¸à¸²à¸£à¸£à¸­à¸š {active_round} à¹ƒà¸«à¹‰à¹€à¸ªà¸£à¹‡à¸ˆà¸à¹ˆà¸­à¸™ à¸ˆà¸¶à¸‡à¸ˆà¸°à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸­à¸š {round_no} à¹„à¸”à¹‰\n"
                        f"à¸—à¸²à¸‡à¹€à¸¥à¸·à¸­à¸ 1: à¸•à¸±à¹‰à¸‡à¸œà¸¥à¸£à¸­à¸š {active_round} à¹ƒà¸«à¸¡à¹ˆà¸”à¹‰à¸§à¸¢ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> à¹à¸¥à¹‰à¸§à¸à¸”à¸¢à¸·à¸™à¸¢à¸±à¸™ /y\n"
                        f"à¸—à¸²à¸‡à¹€à¸¥à¸·à¸­à¸ 2: à¸žà¸´à¸¡à¸žà¹Œ à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™ {active_round} à¹à¸¥à¹‰à¸§à¸„à¹ˆà¸­à¸¢à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸­à¸š {round_no}"
                    )); return

            # à¸–à¹‰à¸²à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¹€à¸„à¸¢à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸£à¸­à¸šà¸™à¸µà¹‰à¸ˆà¸£à¸´à¸‡ à¸«à¹‰à¸²à¸¡à¸¢à¹‰à¸­à¸™ à¹€à¸žà¸£à¸²à¸°à¹„à¸¡à¹ˆà¸¡à¸µà¸œà¸¥à¹ƒà¸«à¹‰à¸¢à¹‰à¸­à¸™
            if not has_round_action("settle", key, round_no):
                safe_reply(event, TextSendMessage(
                    f"âŒ à¸£à¸­à¸š {round_no} à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¹„à¸”à¹‰à¸­à¸­à¸à¸œà¸¥ à¸«à¸£à¸·à¸­à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸£à¸²à¸¢à¸à¸²à¸£à¸ªà¸£à¸¸à¸›à¸œà¸¥à¸—à¸µà¹ˆà¸¢à¸·à¸™à¸¢à¸±à¸™à¹à¸¥à¹‰à¸§\n"
                    f"à¸¢à¹‰à¸­à¸™à¸œà¸¥à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¸£à¸­à¸šà¸—à¸µà¹ˆà¸­à¸­à¸à¸œà¸¥à¹à¸¥à¹‰à¸§à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™"
                )); return

            backup_file = os.path.join(DATA_DIR, f"backup_round_{round_no}.json")
            if not os.path.exists(backup_file):
                safe_reply(event, TextSendMessage(
                    f"âŒ à¹„à¸¡à¹ˆà¸žà¸šà¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¸ªà¸³à¸£à¸­à¸‡à¸‚à¸­à¸‡à¸£à¸­à¸š {round_no}\n"
                    f"à¹„à¸¡à¹ˆà¸ªà¸²à¸¡à¸²à¸£à¸–à¸¢à¹‰à¸­à¸™à¸œà¸¥à¹„à¸”à¹‰ à¹€à¸žà¸·à¹ˆà¸­à¸›à¹‰à¸­à¸‡à¸à¸±à¸™à¹€à¸„à¸£à¸”à¸´à¸•à¹€à¸žà¸µà¹‰à¸¢à¸™"
                )); return

            # à¹€à¸à¹‡à¸š snapshot à¸›à¸±à¸ˆà¸ˆà¸¸à¸šà¸±à¸™à¹„à¸§à¹‰à¸à¹ˆà¸­à¸™ rollback à¹€à¸žà¸·à¹ˆà¸­à¹ƒà¸«à¹‰à¸„à¸³à¸ªà¸±à¹ˆà¸‡ 'à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™ <à¸£à¸­à¸š>' à¸„à¸·à¸™à¸à¸¥à¸±à¸šà¹„à¸”à¹‰
            try:
                save_pending_rollback_snapshot(key, round_no, uid, st)
            except Exception:
                safe_reply(event, TextSendMessage(
                    f"âŒ à¹€à¸•à¸£à¸µà¸¢à¸¡à¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™à¸£à¸­à¸š {round_no} à¹„à¸¡à¹ˆà¸ªà¸³à¹€à¸£à¹‡à¸ˆ\n"
                    f"à¸£à¸°à¸šà¸šà¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¢à¹‰à¸­à¸™à¸œà¸¥ à¹€à¸žà¸·à¹ˆà¸­à¸›à¹‰à¸­à¸‡à¸à¸±à¸™à¹€à¸„à¸£à¸”à¸´à¸•à¹€à¸žà¸µà¹‰à¸¢à¸™"
                )); return

            claimed, old_action = claim_round_action("rollback", key, round_no, uid)
            if not claimed:
                clear_pending_rollback_snapshot(key)
                safe_reply(event, TextSendMessage(
                    f"âš ï¸ à¸£à¸­à¸š {round_no} à¸–à¸¹à¸à¸¢à¹‰à¸­à¸™à¸œà¸¥à¹„à¸›à¹à¸¥à¹‰à¸§ à¸«à¸£à¸·à¸­à¸à¸³à¸¥à¸±à¸‡à¸–à¸¹à¸à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸­à¸¢à¸¹à¹ˆ\n"
                    f"à¸•à¹‰à¸­à¸‡à¸­à¸­à¸à¸œà¸¥à¸£à¸­à¸š {round_no} à¹ƒà¸«à¸¡à¹ˆà¹ƒà¸«à¹‰à¹€à¸ªà¸£à¹‡à¸ˆà¸à¹ˆà¸­à¸™ à¸«à¹‰à¸²à¸¡à¸¢à¹‰à¸­à¸™à¸‹à¹‰à¸³"
                )); return

            try:
                with open(backup_file, "rb") as f:
                    data = _loads_bytes(f.read())

                # âœ… à¸„à¸·à¸™à¹€à¸„à¸£à¸”à¸´à¸•à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”
                with with_users_lock():
                    users.clear()
                    users.update(data["users"])
                save_users_persist()

                # âœ… à¸„à¸·à¸™à¸ªà¸–à¸²à¸™à¸°à¸«à¹‰à¸­à¸‡ (à¸šà¸´à¸¥, à¸¢à¸­à¸”à¸£à¸§à¸¡ à¸¯à¸¥à¸¯)
                st.update(data.get("room_state", {}))
                st["phase"] = "PAUSED"
                st["settling"] = False
                st["pendingCode"] = None  # à¸šà¸±à¸‡à¸„à¸±à¸šà¹ƒà¸«à¹‰à¹à¸­à¸”à¸¡à¸´à¸™à¸•à¸±à¹‰à¸‡à¸œà¸¥à¹ƒà¸«à¸¡à¹ˆ à¹„à¸¡à¹ˆà¹ƒà¸Šà¹‰à¸œà¸¥à¹€à¸à¹ˆà¸²à¹‚à¸”à¸¢à¹„à¸¡à¹ˆà¸•à¸±à¹‰à¸‡à¹ƒà¸ˆ

                # âœ… à¸„à¸·à¸™à¸„à¹ˆà¸²à¸à¸³à¹„à¸£à¸ªà¸°à¸ªà¸¡ (METRICS)
                if "metrics" in data:
                    METRICS.clear()
                    METRICS.update(data["metrics"])

                # à¸›à¸¥à¸”à¸¥à¹‡à¸­à¸ settle à¹€à¸”à¸´à¸¡ à¹€à¸žà¸£à¸²à¸°à¸£à¸­à¸šà¸™à¸µà¹‰à¸–à¸¹à¸à¸¢à¹‰à¸­à¸™à¸à¸¥à¸±à¸šà¸¡à¸²à¹à¸¥à¹‰à¸§ à¸•à¹‰à¸­à¸‡à¸­à¸™à¸¸à¸à¸²à¸•à¹ƒà¸«à¹‰à¸­à¸­à¸à¸œà¸¥à¹ƒà¸«à¸¡à¹ˆà¹„à¸”à¹‰
                release_round_action("settle", key, round_no)

                safe_reply(event, TextSendMessage(
                    f"âœ… à¸¢à¹‰à¸­à¸™à¹€à¸„à¸£à¸”à¸´à¸•à¹à¸¥à¸°à¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¸£à¸­à¸š {round_no} à¸ªà¸³à¹€à¸£à¹‡à¸ˆà¹à¸¥à¹‰à¸§\n"
                    f"à¸‚à¸±à¹‰à¸™à¸•à¸­à¸™à¸•à¹ˆà¸­à¹„à¸›: à¸žà¸´à¸¡à¸žà¹Œ s<à¸£à¸«à¸±à¸ªà¸œà¸¥> à¹à¸¥à¹‰à¸§à¸à¸”à¸¢à¸·à¸™à¸¢à¸±à¸™ /y\n"
                    f"à¸–à¹‰à¸²à¹„à¸¡à¹ˆà¸•à¹‰à¸­à¸‡à¸à¸²à¸£à¸¢à¹‰à¸­à¸™à¹à¸¥à¹‰à¸§ à¹ƒà¸«à¹‰à¸žà¸´à¸¡à¸žà¹Œ: à¸¢à¸à¹€à¸¥à¸´à¸à¸¢à¹‰à¸­à¸™ {round_no}\n"
                    f"à¸£à¸°à¸«à¸§à¹ˆà¸²à¸‡à¸™à¸µà¹‰à¸«à¹‰à¸²à¸¡à¸¢à¹‰à¸­à¸™à¸£à¸­à¸šà¸­à¸·à¹ˆà¸™à¸ˆà¸™à¸à¸§à¹ˆà¸²à¸ˆà¸°à¸ˆà¸±à¸”à¸à¸²à¸£à¸£à¸­à¸š {round_no} à¹ƒà¸«à¹‰à¹€à¸ªà¸£à¹‡à¸ˆ"
                )); return
            except Exception:
                # à¸–à¹‰à¸²à¸¢à¹‰à¸­à¸™à¸¥à¹‰à¸¡à¹€à¸«à¸¥à¸§ à¹ƒà¸«à¹‰à¸›à¸¥à¸”à¸¥à¹‡à¸­à¸ rollback à¹€à¸žà¸·à¹ˆà¸­à¹ƒà¸«à¹‰à¹à¸à¹‰à¹„à¸‚/à¸¥à¸­à¸‡à¹ƒà¸«à¸¡à¹ˆà¹„à¸”à¹‰ à¹„à¸¡à¹ˆà¹ƒà¸«à¹‰à¸„à¹‰à¸²à¸‡à¸–à¸²à¸§à¸£
                release_round_action("rollback", key, round_no)
                clear_pending_rollback_snapshot(key)
                app.logger.exception("rollback failed")
                safe_reply(event, TextSendMessage(
                    f"âŒ à¸¢à¹‰à¸­à¸™à¸œà¸¥à¸£à¸­à¸š {round_no} à¹„à¸¡à¹ˆà¸ªà¸³à¹€à¸£à¹‡à¸ˆ à¸£à¸°à¸šà¸šà¸¢à¸à¹€à¸¥à¸´à¸à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹à¸¥à¹‰à¸§"
                )); return



        if text.strip().lower() == "call":
            if not gid or not is_backoffice_group_id(gid):
                return

            with with_users_lock():
                table = [u for u in users.values() if int(u.get("credit", 0) or 0) > 0]

            if not table:
                safe_reply(event, TextSendMessage("à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸¥à¸¹à¸à¸„à¹‰à¸²à¸—à¸µà¹ˆà¸¡à¸µà¹€à¸„à¸£à¸”à¸´à¸•"))
                return

            table = sorted(table, key=lambda x: (-int(x.get("credit", 0) or 0), int(x.get("cid", 0) or 0)))
            table = table[:100]

            msg = format_user_table(table)

            safe_reply(event, TextSendMessage(msg))
            return


        # ==== à¸¢à¸à¹€à¸¥à¸´à¸à¸šà¸´à¸¥ ====
        m_cancel_by_cid = re.match(r"^x\s+(\d+)$", text.strip(), re.IGNORECASE)
        # à¹€à¸Šà¹‡à¸„à¸§à¹ˆà¸²à¹€à¸›à¹‡à¸™à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸¢à¸à¹€à¸¥à¸´à¸à¸«à¸£à¸·à¸­à¹„à¸¡à¹ˆ
        if text.strip().lower() in ("xx", "x*") or m_cancel_by_cid or text.strip().upper() == "X":
            if st["phase"] == "NONE":
                safe_reply(event, TextSendMessage("à¸¢à¸à¹€à¸¥à¸´à¸à¹„à¸¡à¹ˆà¹„à¸”à¹‰: à¸£à¸­à¸šà¸™à¸µà¹‰à¸ªà¸£à¸¸à¸›à¸ˆà¸šà¹à¸¥à¹‰à¸§")); return

            # à¹à¸­à¸”à¸¡à¸´à¸™à¸¢à¸à¹€à¸¥à¸´à¸à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”
            if text.strip().lower() in ("xx", "x*"):
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return
                n = len(st["bet_index"])
                # à¸„à¸·à¸™ escrow à¸—à¸¸à¸à¸„à¸™
                with with_users_lock():
                    for tuid, esc_amt in list(st["escrow"].items()):
                        if esc_amt > 0 and tuid in users:
                            users[tuid]["credit"] = users[tuid].get("credit", 0) + esc_amt
                    st["escrow"].clear()
                    st["bet_index"].clear()
                    st["totals"] = {"HI": 0, "LO": 0}
                    save_users_persist()
                extra = " (à¸à¸³à¸¥à¸±à¸‡à¸žà¸±à¸à¸£à¸­à¸š)" if st["phase"] == "PAUSED" else ""
                safe_reply(event, TextSendMessage(f"à¸¢à¸à¹€à¸¥à¸´à¸à¸šà¸´à¸¥à¸—à¸±à¹‰à¸‡à¸«à¸¡à¸”à¸ªà¸³à¹€à¸£à¹‡à¸ˆ{extra} ({n} à¸šà¸´à¸¥)")); return

            # à¹à¸­à¸”à¸¡à¸´à¸™à¸¢à¸à¹€à¸¥à¸´à¸à¸•à¸²à¸¡ ID à¸¥à¸¹à¸à¸„à¹‰à¸²
            if m_cancel_by_cid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¸™à¸µà¹‰à¹ƒà¸Šà¹‰à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹à¸­à¸”à¸¡à¸´à¸™")); return
                cid = int(m_cancel_by_cid.group(1))
                with with_users_lock():
                    target = get_user_by_cid(cid)
                    if not target:
                        safe_reply(event, TextSendMessage(f"à¹„à¸¡à¹ˆà¸žà¸š ID {cid}")); return
                    tuid = target["uid"]
                    bet = st["bet_index"].pop(tuid, None)
                    if not bet:
                        safe_reply(event, TextSendMessage(f"ID {cid} à¹„à¸¡à¹ˆà¸¡à¸µà¸šà¸´à¸¥à¹ƒà¸™à¸£à¸­à¸šà¸™à¸µà¹‰")); return

                    st["totals"][bet["side"]] -= bet["amount"]
                    esc = st["escrow"].get(tuid, 0)
                    refund = min(esc, bet["amount"])
                    if refund > 0:
                        users[tuid]["credit"] = users[tuid].get("credit", 0) + refund
                        st["escrow"][tuid] = esc - refund
                        if st["escrow"][tuid] <= 0:
                            st["escrow"].pop(tuid, None)
                    save_users_persist()
                extra = " (à¸à¸³à¸¥à¸±à¸‡à¸žà¸±à¸à¸£à¸­à¸š)" if st["phase"] == "PAUSED" else ""
                safe_reply(event, TextSendMessage(f"à¸¢à¸à¹€à¸¥à¸´à¸à¸šà¸´à¸¥à¸‚à¸­à¸‡ ID {cid} à¸ªà¸³à¹€à¸£à¹‡à¸ˆ{extra} ({'à¸ªà¸¹à¸‡' if bet['side']=='HI' else 'à¸•à¹ˆà¸³'} {fmt(bet['amount'])})")); return

            # à¸¥à¸¹à¸à¸„à¹‰à¸²à¸¢à¸à¹€à¸¥à¸´à¸à¸šà¸´à¸¥à¸•à¸±à¸§à¹€à¸­à¸‡
            if text.strip().upper() == "X":
                if st["phase"] == "PAUSED":
                    safe_reply(event, TextSendMessage("à¸à¸³à¸¥à¸±à¸‡à¸žà¸±à¸à¸£à¸­à¸š: à¸¥à¸¹à¸à¸„à¹‰à¸²à¹„à¸¡à¹ˆà¸ªà¸²à¸¡à¸²à¸£à¸–à¸¢à¸à¹€à¸¥à¸´à¸à¹„à¸”à¹‰ à¹‚à¸›à¸£à¸”à¹ƒà¸«à¹‰à¹à¸­à¸”à¸¡à¸´à¸™à¸”à¸³à¹€à¸™à¸´à¸™à¸à¸²à¸£")); return
                bet = st["bet_index"].pop(uid, None)
                if not bet:
                    safe_reply(event, TextSendMessage("à¸„à¸¸à¸“à¸¢à¸±à¸‡à¹„à¸¡à¹ˆà¸¡à¸µà¸à¸²à¸£à¹€à¸”à¸´à¸¡à¸žà¸±à¸™à¹ƒà¸™à¸£à¸­à¸šà¸™à¸µà¹‰")); return

                with with_users_lock():
                    st["totals"][bet["side"]] -= bet["amount"]
                    esc = st["escrow"].get(uid, 0)
                    refund = min(esc, bet["amount"])
                    if refund > 0:
                        users[uid]["credit"] = users[uid].get("credit", 0) + refund
                        st["escrow"][uid] = esc - refund
                        if st["escrow"][uid] <= 0:
                            st["escrow"].pop(uid, None)
                    save_users_persist()
                
                try:
                    profile = line_bot_api.get_profile(uid)
                    line_name = profile.display_name
                except Exception:
                    line_name = users.get(uid, {}).get("name", "à¹„à¸¡à¹ˆà¸—à¸£à¸²à¸šà¸Šà¸·à¹ˆà¸­")
                safe_reply(event, TextSendMessage(f"à¸„à¸¸à¸“ {line_name} âŒà¸¢à¸à¹€à¸¥à¸´à¸à¸à¸²à¸£à¹€à¸”à¸´à¸¡à¸žà¸±à¸™à¹€à¸”à¸´à¸¡à¸ªà¸³à¹€à¸£à¹‡à¸ˆâŒ ({'à¸ªà¸¹à¸‡' if bet['side']=='HI' else 'à¸•à¹ˆà¸³'} {fmt(bet['amount'])})")); return

        # ==== FAST PATH: à¸ªà¹ˆà¸§à¸™à¸™à¸µà¹‰à¸•à¹‰à¸­à¸‡à¸­à¸¢à¸¹à¹ˆà¸™à¸­à¸ if à¸”à¹‰à¸²à¸™à¸šà¸™ ====
        bet = parse_bet(text)
        if bet:
            # à¹à¸­à¸”à¸¡à¸´à¸™à¹€à¸¥à¹ˆà¸™à¹„à¸”à¹‰ (à¸›à¸´à¸”à¸à¸²à¸£à¹€à¸Šà¹‡à¸„ is_admin à¹„à¸§à¹‰à¹à¸¥à¹‰à¸§)
            # if is_admin(uid):
            #     return
            
            with with_users_lock(): # [FIXED] à¹ƒà¸Šà¹‰à¹à¸„à¹ˆ with_users_lock()
                if uid not in users:
                    safe_reply(event, TextSendMessage("à¸à¸£à¸¸à¸“à¸²à¸žà¸´à¸¡à¸žà¹Œ add à¹€à¸žà¸·à¹ˆà¸­à¸£à¸±à¸šà¹„à¸­à¸”à¸µà¸à¹ˆà¸­à¸™à¸§à¸²à¸‡à¸šà¸´à¸¥")); return

                ok, why = can_bet(st, uid, bet["side"], bet["amount"])
                if not ok:
                    safe_reply(event, TextSendMessage(f"âŒà¸£à¸±à¸šà¸šà¸´à¸¥à¹„à¸¡à¹ˆà¹„à¸”à¹‰âŒ: {why}")); return

                u = users[uid]
                if u.get("credit", 0) < bet["amount"]:
                    safe_reply(event, TextSendMessage(f"à¸—à¸¸à¸™à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­à¹„à¸¡à¹ˆà¸žà¸­ (à¸¡à¸µ {fmt(u.get('credit',0))})")); return

                u["credit"] -= bet["amount"]
                st["escrow"][uid] = st["escrow"].get(uid, 0) + bet["amount"]
                save_users_persist()

                name = u["name"]
                st["bet_index"][uid] = {"uid": uid, "name": name, "side": bet["side"], "amount": bet["amount"]}
                st["totals"][bet["side"]] += bet["amount"]

                side_th = "à¸ªà¸¹à¸‡" if bet["side"] == "HI" else "à¸•à¹ˆà¸³"
                safe_reply(event, TextSendMessage(
                    f"à¸„à¸¸à¸“ {name} âœ… à¹€à¸¥à¹ˆà¸™ {side_th} = {fmt(bet['amount'])} â€¢ à¸¢à¸­à¸”à¹€à¸‡à¸´à¸™à¸„à¸‡à¹€à¸«à¸¥à¸·à¸­ {fmt(u['credit'])}"
                )); return


    # ----- à¸—à¸µà¹ˆà¹€à¸«à¸¥à¸·à¸­à¸„à¹ˆà¸­à¸¢à¹„à¸›à¹€à¸Šà¹‡à¸„à¸„à¸³à¸ªà¸±à¹ˆà¸‡à¹à¸­à¸”à¸¡à¸´à¸™/à¸¢à¸¹à¸—à¸´à¸¥à¸•à¹ˆà¸²à¸‡à¹† à¹€à¸«à¸¡à¸·à¸­à¸™à¹€à¸”à¸´à¸¡ -----

@handler.add(MessageEvent, message=ImageMessage)
def on_image(event: MessageEvent):
    uid = event.source.user_id
    gid = getattr(event.source, "group_id", None)
    key = room_key(event.source)

    # à¸à¸±à¸™ LINE retry / webhook à¸‹à¹‰à¸³: message id à¹€à¸”à¸´à¸¡à¸•à¹‰à¸­à¸‡à¹„à¸¡à¹ˆà¸–à¸¹à¸à¸›à¸£à¸°à¸¡à¸§à¸¥à¸œà¸¥à¸‹à¹‰à¸³
    if already_processed_message(getattr(event.message, "id", None)):
        return

    # à¸•à¹‰à¸­à¸‡à¸­à¸¢à¸¹à¹ˆà¹ƒà¸™à¸à¸¥à¸¸à¹ˆà¸¡/à¸«à¹‰à¸­à¸‡à¹€à¸—à¹ˆà¸²à¸™à¸±à¹‰à¸™
    if not in_group_or_room(event.source):
        return

    # à¸•à¸£à¸§à¸ˆ allow/deny/lockdown à¸‚à¸­à¸‡à¸à¸¥à¸¸à¹ˆà¸¡
    if gid:
        if gid in BANNED_GROUPS or gid in DENY_GROUP_IDS:
            return
        if not is_allowed_group(gid):
            return
        if _locked_group(gid) and not is_admin(uid):
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("à¸£à¸°à¸šà¸š: à¸à¸¥à¸¸à¹ˆà¸¡à¸à¸³à¸¥à¸±à¸‡à¸¥à¹‡à¸­à¸à¸”à¸²à¸§à¸™à¹Œà¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§ à¸•à¸´à¸”à¸•à¹ˆà¸­à¹à¸­à¸”à¸¡à¸´à¸™à¹€à¸žà¸·à¹ˆà¸­à¸›à¸¥à¸”à¸¥à¹‡à¸­à¸"))
            return

    # à¸•à¸£à¸§à¸ˆà¸ªà¸–à¸²à¸™à¸°à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰ ban/mute
    if uid in BANNED_UIDS:
        return
    if _muted(uid):
        if not _notice_throttled(uid):
            safe_reply(event, TextSendMessage("à¸£à¸°à¸šà¸š: à¸„à¸¸à¸“à¸–à¸¹à¸à¸ˆà¸³à¸à¸±à¸”à¸à¸²à¸£à¸ªà¹ˆà¸‡à¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸Šà¸±à¹ˆà¸§à¸„à¸£à¸²à¸§ (anti-spam)"))
        return

    # rate limit à¹à¸šà¸šà¹€à¸”à¸µà¸¢à¸§à¸à¸±à¸šà¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸•à¸±à¸§à¸«à¸™à¸±à¸‡à¸ªà¸·à¸­
    if not rl.allow(f"room:{key}", RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD):
        return
    if not rl.allow(f"uid:{uid}:burst", RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD) or \
       not rl.allow(f"uid:{uid}:day", RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD):
        STRIKES[uid] = STRIKES.get(uid, 0) + 1
        if STRIKES[uid] >= ABUSE_STRIKE_TO_MUTE:
            MUTED_UNTIL[uid] = _now() + MUTE_SECONDS_DEFAULT
            STRIKES[uid] = 0
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage(f"à¸£à¸°à¸šà¸š: à¸¡à¸´à¸§à¸—à¹Œ {MUTE_SECONDS_DEFAULT} à¸§à¸´à¸™à¸²à¸—à¸µ à¹€à¸™à¸·à¹ˆà¸­à¸‡à¸ˆà¸²à¸à¸à¸´à¸ˆà¸à¸£à¸£à¸¡à¸–à¸µà¹ˆà¸œà¸´à¸”à¸›à¸à¸•à¸´"))
        else:
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("à¸£à¸°à¸šà¸š: à¸à¸´à¸ˆà¸à¸£à¸£à¸¡à¸–à¸µà¹ˆà¹€à¸à¸´à¸™à¸à¸³à¸«à¸™à¸” à¸Šà¹ˆà¸§à¸¢à¹€à¸§à¹‰à¸™à¸Šà¹ˆà¸§à¸‡à¸«à¸™à¹ˆà¸­à¸¢à¸™à¸°"))
        return

    # à¹€à¸•à¸£à¸µà¸¢à¸¡ state à¸«à¹‰à¸­à¸‡
    with with_rooms_lock():
        if key not in rooms:
            rooms[key] = start_state()
        st = rooms[key]

    # à¸•à¹‰à¸­à¸‡à¸¡à¸µà¸‚à¹‰à¸­à¸¡à¸¹à¸¥à¸œà¸¹à¹‰à¹ƒà¸Šà¹‰à¸à¹ˆà¸­à¸™ (à¸žà¸´à¸¡à¸žà¹Œ add à¸¡à¸²à¸à¹ˆà¸­à¸™)
    with with_users_lock():
        u = users.get(uid)

    if not u:
        safe_reply(event, TextSendMessage("à¸à¸£à¸¸à¸“à¸²à¸žà¸´à¸¡à¸žà¹Œ add à¹€à¸žà¸·à¹ˆà¸­à¸£à¸±à¸šà¹„à¸­à¸”à¸µà¸à¹ˆà¸­à¸™"))
        return

    # à¸•à¸­à¸šà¸à¸²à¸£à¹Œà¸” C à¸‚à¸­à¸‡à¸œà¸¹à¹‰à¸—à¸µà¹ˆà¸ªà¹ˆà¸‡à¸£à¸¹à¸›
    try:
        safe_reply(event, flex_customer_card(st, u))
    except Exception:
        # à¸à¸±à¸™à¸•à¸ à¸–à¹‰à¸² Flex error à¹ƒà¸«à¹‰à¸•à¸­à¸šà¸‚à¹‰à¸­à¸„à¸§à¸²à¸¡à¸˜à¸£à¸£à¸¡à¸”à¸² à¹‚à¸”à¸¢à¹„à¸¡à¹ˆà¹ƒà¸«à¹‰à¸žà¸±à¸‡à¸‹à¹‰à¸³à¸–à¹‰à¸² u à¸«à¸²à¸¢
        app.logger.exception("on_image flex_customer_card failed uid=%s", uid)
        cid = u.get('cid', '-') if isinstance(u, dict) else '-'
        name = u.get('name', 'à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™') if isinstance(u, dict) else 'à¸œà¸¹à¹‰à¹€à¸¥à¹ˆà¸™'
        credit = u.get('credit', 0) if isinstance(u, dict) else 0
        safe_reply(event, TextSendMessage(
            f"ID {cid} â€¢ {name} â€¢ à¹€à¸„à¸£à¸”à¸´à¸• {fmt(credit)} à¸š."
        ))


def current_camp(st):
    return (st.get("price", {}) or {}).get("camp") or (st.get("note") or "à¹„à¸¡à¹ˆà¸£à¸°à¸šà¸¸à¸„à¹ˆà¸²à¸¢")

def push_batch(to_id, messages, batch=5):
    for i in range(0, len(messages), batch):
        safe_push(to_id, messages[i:i+batch])



# ====== ANTI-KICK MONITOR ======
@handler.add(MemberLeftEvent)
def on_member_left(event: MemberLeftEvent):
    gid = getattr(event.source, "group_id", None)
    if not gid: return
    try:
        members = getattr(getattr(event, "left", None), "members", []) or []
    except Exception:
        members = []
    left_uids = []
    for m in members:
        uid = getattr(m, "user_id", None) or getattr(m, "mid", None) or getattr(m, "id", None)
        if uid: left_uids.append(uid)
    for lu in left_uids:
        if lu in PROTECTED_UIDS:
            _lockdown_and_alert(gid, lu)
            break
    


# ====== FREE BACKOFFICE VIEW (no LINE quota) ======
# à¹€à¸›à¸´à¸”à¸”à¸¹à¸ªà¸£à¸¸à¸›à¸¥à¹ˆà¸²à¸ªà¸¸à¸”à¸œà¹ˆà¸²à¸™à¹€à¸§à¹‡à¸š: /backoffice/latest?token=YOURTOKEN
# à¸•à¸±à¹‰à¸‡ token à¹„à¸”à¹‰à¸”à¹‰à¸§à¸¢ env: BACKOFFICE_VIEW_TOKEN (à¸–à¹‰à¸²à¹„à¸¡à¹ˆà¸•à¸±à¹‰à¸‡ à¸ˆà¸°à¹€à¸›à¸´à¸”à¹„à¸”à¹‰à¹€à¸‰à¸žà¸²à¸°à¹ƒà¸™à¸§à¸‡à¹à¸¥à¸™/à¹€à¸„à¸£à¸·à¹ˆà¸­à¸‡à¸•à¸±à¸§à¹€à¸­à¸‡à¸•à¸²à¸¡à¹„à¸Ÿà¸£à¹Œà¸§à¸­à¸¥à¸¥à¹Œ)
@app.route("/backoffice/latest", methods=["GET"])
def backoffice_latest():
    token = os.getenv("BACKOFFICE_VIEW_TOKEN", "").strip()
    if token:
        if request.args.get("token", "").strip() != token:
            return make_response("forbidden", 403)

    p = load_last_settle()
    if not p:
        return make_response(json.dumps({"ok": False, "message": "no last_settle yet"}, ensure_ascii=False),
                             404, {"Content-Type": "application/json; charset=utf-8"})

    return make_response(json.dumps({"ok": True, "data": p}, ensure_ascii=False),
                         200, {"Content-Type": "application/json; charset=utf-8"})

if __name__ == "__main__":
    port = int(os.getenv("PORT", 5000))
    print(f"Starting Waitress on 0.0.0.0:{port}")
    serve(
        app,
        host="0.0.0.0",
        port=port,
        threads=16,
        connection_limit=200,
        channel_timeout=60
    )



