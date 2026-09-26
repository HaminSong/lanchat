#!/usr/bin/env python3
"""
LAN Chat — 로컬망 메신저 (PC 데스크톱 앱 + 폰 브라우저)

• PC마다 실행하면 같은 네트워크의 PC들을 자동으로 찾아 목록에 표시합니다 (서버 불필요).
• 상대를 누르면 1:1 대화창이 열리고, 채팅과 파일 전송을 할 수 있습니다.
• 폰은 아무 PC의 "폰 연결" 주소(QR)로 브라우저 접속하면 같은 목록에 참여합니다.
• 상대가 꺼져 있으면 메시지는 대기했다가 접속하는 순간 전달됩니다.

필요 패키지:  pip install pywebview segno
빌드:        py -m PyInstaller --onefile --noconsole --name LANChat lanchat.py

실행 옵션:
  (없음)        데스크톱 창으로 실행
  --browser     창 대신 기본 브라우저로 실행
  --server      창 없이 서버만 실행 (콘솔)
"""
import argparse
import getpass
import io
import json
import logging
import mimetypes
import os
import queue
import re
import secrets
import shutil
import socket
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request
import uuid
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, quote, urlencode, urlparse

APP = "lanchat"
PROTO = 2
UDP_PORT = 50505
LOCK_PORT = 50506
BEACON_INTERVAL = 2.0
PEER_TIMEOUT = 7.0
WEB_USER_KEEP_DAYS = 14
MAX_UPLOAD = 4 * 1024 ** 3
MAX_TEXT = 20000
HISTORY_LIMIT = 1000
FID_RE = re.compile(r"^[0-9a-f]{32}$")
STATUSES = ("online", "away", "busy")
WIN_RESERVED = {"CON", "PRN", "AUX", "NUL"} | {"COM%d" % i for i in range(1, 10)} | {"LPT%d" % i for i in range(1, 10)}
MSG_FIELDS = ("mid", "frm", "to", "frm_name", "to_name", "type", "text", "fid", "fname", "size", "mime", "ts")

log = logging.getLogger("lanchat")
NO_PROXY = urllib.request.build_opener(urllib.request.ProxyHandler({}))


def base_dir():
    if getattr(sys, "frozen", False):
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__))


def default_data_dir():
    """설치형(exe)은 사용자 AppData에, 스크립트 실행은 파일 옆에 저장"""
    if getattr(sys, "frozen", False):
        root = os.environ.get("APPDATA") or os.path.expanduser("~")
        return os.path.join(root, "LANChat")
    return os.path.join(base_dir(), "lanchat_data")


def node_of(uid):
    return str(uid).split(":", 1)[0]


def safe_fname(name):
    name = os.path.basename(str(name or "").replace("\\", "/"))
    name = re.sub(r'[\x00-\x1f<>:"/\\|?*]', "_", name).strip().rstrip(". ")
    if not name:
        name = "file"
    stem, ext = os.path.splitext(name)
    if stem.upper() in WIN_RESERVED:
        name = "_" + name
        stem = "_" + stem
    if len(name) > 150:
        ext = ext[:20]
        name = stem[:150 - len(ext)] + ext
    return name


def documents_dir():
    if os.name == "nt":
        try:
            import ctypes
            buf = ctypes.create_unicode_buffer(1024)
            if ctypes.windll.shell32.SHGetFolderPathW(None, 5, None, 0, buf) == 0 and buf.value:
                return buf.value  # CSIDL_PERSONAL = 문서 (OneDrive로 옮겨진 경우 포함)
        except Exception:
            pass
    return os.path.join(os.path.expanduser("~"), "Documents")


def unique_path(folder, fname):
    stem, ext = os.path.splitext(fname)
    path = os.path.join(folder, fname)
    i = 1
    while os.path.exists(path) or os.path.exists(path + ".part"):
        path = os.path.join(folder, "%s (%d)%s" % (stem, i, ext))
        i += 1
    return path


KO = False   # 기본 언어는 영어 (사용자가 앱에서 한국어를 고르면 desk_korean()이 True)


def tr(ko, en):
    return ko if KO else en


def default_name():
    try:
        n = getpass.getuser()
    except Exception:
        n = ""
    return (n or socket.gethostname() or "PC")[:30]


def lan_ips():
    primary = None
    ips = []
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        primary = s.getsockname()[0]
        s.close()
    except OSError:
        pass
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.append(info[4][0])
    except OSError:
        pass
    out = []
    for ip in ([primary] if primary else []) + ips:
        if ip and not ip.startswith("127.") and ip not in out:
            out.append(ip)
    return out


def clean_user(u, nid):
    if not isinstance(u, dict):
        return None
    uid = str(u.get("uid", ""))[:80]
    if node_of(uid) != nid:
        return None
    st = u.get("status")
    return {
        "uid": uid,
        "name": str(u.get("name", "") or "?")[:30],
        "status": st if st in STATUSES else "online",
        "note": str(u.get("note", "") or "")[:60],
        "kind": "mobile" if u.get("kind") == "mobile" else "pc",
        "online": bool(u.get("online", True)),
    }


class Sub:
    def __init__(self, uid):
        self.uid = uid
        self.q = queue.Queue()
        self.last = None


# ====================================================================== node
class Node:
    def __init__(self, data_dir, port=8000, udp_port=UDP_PORT, extra_peers=(), name=None, recv_dir=None):
        self.data_dir = data_dir
        self.files_dir = os.path.join(data_dir, "files")      # 폰·전달용 임시 보관
        os.makedirs(self.files_dir, exist_ok=True)
        self.recv_dir = recv_dir or os.path.join(documents_dir(), "LAN Chat")  # 이 PC가 받은 파일
        self.findex_path = os.path.join(data_dir, "files.json")
        try:
            with open(self.findex_path, encoding="utf-8") as f:
                self.findex = json.load(f)
        except (OSError, ValueError):
            self.findex = {}
        self.cfg_path = os.path.join(data_dir, "config.json")
        self.log_path = os.path.join(data_dir, "messages.jsonl")
        self.lock = threading.RLock()
        self.want_port = port
        self.port = None
        self.udp_port = udp_port
        self.extra_peers = list(extra_peers)
        self.desk_token = secrets.token_hex(16)
        self.native = False
        self.on_incoming = None
        self.running = False

        self.cfg = self._load_cfg()
        if name:
            self.cfg["desk"]["name"] = name[:30]
        self.node_id = self.cfg["node_id"]
        self.tokens = {t: u["uid"] for t, u in self.cfg["web"].items()}

        self.messages = []
        self.by_mid = {}
        self.pending = {}
        self.files = {}
        self.seq = 0
        self.peers = {}
        self.subs = set()
        self.online_web = {}
        self.inflight = set()
        self.retry_at = {}
        self.version = 0
        self.pushed_version = -1
        self.wake = threading.Event()
        self.beacon_now = threading.Event()
        self._load_messages()
        self._save_cfg()

    # ------------------------------------------------------------ persistence
    def _load_cfg(self):
        try:
            with open(self.cfg_path, encoding="utf-8") as f:
                cfg = json.load(f)
            if not isinstance(cfg, dict):
                cfg = {}
        except (OSError, ValueError):
            cfg = {}
        cfg.setdefault("node_id", uuid.uuid4().hex[:12])
        cfg.setdefault("desk", {})
        cfg["desk"].setdefault("name", default_name())
        cfg["desk"].setdefault("status", "online")
        cfg["desk"].setdefault("note", "")
        cfg.setdefault("web", {})
        cfg.setdefault("reads", {})
        cfg.setdefault("cleared", {})
        return cfg

    def _save_cfg(self):
        with self.lock:
            tmp = self.cfg_path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.cfg, f, ensure_ascii=False, indent=1)
            os.replace(tmp, self.cfg_path)

    def _load_messages(self):
        if not os.path.exists(self.log_path):
            return
        with open(self.log_path, encoding="utf-8") as f:
            for line in f:
                try:
                    rec = json.loads(line)
                except ValueError:
                    continue
                mid = rec.get("mid")
                if not mid:
                    continue
                if mid in self.by_mid:
                    n = self.by_mid[mid]["n"]
                    self.by_mid[mid].update(rec)
                    self.by_mid[mid]["n"] = n
                else:
                    if isinstance(rec.get("n"), int) and rec["n"] > self.seq:
                        self.seq = rec["n"]          # 저장된 번호 유지 (삭제 후에도 번호가 밀리지 않게)
                    else:
                        self.seq += 1
                        rec["n"] = self.seq
                    self.messages.append(rec)
                    self.by_mid[mid] = rec
        for m in self.messages:
            if m.get("st") == "pending":
                self.pending[m["mid"]] = m
            if m.get("type") == "file":
                self._index_file(m)

    def _index_file(self, m):
        path = self.findex.get(m["fid"]) or os.path.join(self.files_dir, m["fid"], m["fname"])
        self.files[m["fid"]] = {"path": path, "fname": m["fname"], "mime": m.get("mime")}

    def _set_file_path(self, fid, path):
        with self.lock:
            self.findex[fid] = path
            if fid in self.files:
                self.files[fid]["path"] = path
            tmp = self.findex_path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.findex, f, ensure_ascii=False)
            os.replace(tmp, self.findex_path)

    def _to_recv_dir(self, src, fname):
        """이 PC 사용자가 받은 파일을 문서\\LAN Chat 으로 이동, 최종 경로 반환"""
        os.makedirs(self.recv_dir, exist_ok=True)
        with self.lock:
            dst = unique_path(self.recv_dir, fname)
            shutil.move(src, dst)
        return dst

    def _append_log(self, m):
        with open(self.log_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(m, ensure_ascii=False) + "\n")

    def _rewrite_log(self):
        tmp = self.log_path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            for m in self.messages:
                f.write(json.dumps(m, ensure_ascii=False) + "\n")
        os.replace(tmp, self.log_path)

    # ------------------------------------------------------------ users
    def _local_users(self, include_stale=False):
        d = self.cfg["desk"]
        out = [{"uid": self.node_id, "name": d["name"], "status": d["status"], "note": d["note"],
                "kind": "pc", "online": True, "lang": d.get("lang", "en")}]
        cutoff = time.time() - WEB_USER_KEEP_DAYS * 86400
        for u in self.cfg["web"].values():
            online = self.online_web.get(u["uid"], 0) > 0
            if not include_stale and not online and u.get("seen", 0) < cutoff:
                continue
            out.append({"uid": u["uid"], "name": u["name"], "status": u.get("status", "online"),
                        "note": u.get("note", ""), "kind": "mobile", "online": online,
                        "lang": u.get("lang", "en")})
        return out

    def _local_uids(self):
        return {self.node_id} | {u["uid"] for u in self.cfg["web"].values()}

    def _all_users(self):
        users = self._local_users()
        for p in self.peers.values():
            users.extend(p["users"])
        return users

    def _web_entry(self, uid):
        for t, u in self.cfg["web"].items():
            if u["uid"] == uid:
                return u
        return None

    def user_info(self, uid):
        with self.lock:
            for u in self._all_users():
                if u["uid"] == uid:
                    return dict(u)
            name = "?"
            for m in self.messages:
                if m["frm"] == uid:
                    name = m.get("frm_name") or name
                elif m["to"] == uid:
                    name = m.get("to_name") or name
            return {"uid": uid, "name": name, "status": "online", "note": "",
                    "kind": "mobile" if ":" in uid else "pc", "online": False}

    def display_name(self, uid):
        return self.user_info(uid)["name"]

    def _cut(self, uid, peer):
        return self.cfg["cleared"].get(uid, {}).get(peer, 0)

    def contacts_for(self, uid):
        with self.lock:
            users = {u["uid"]: dict(u) for u in self._all_users() if u["uid"] != uid}
            reads = self.cfg["reads"].get(uid, {})
            cleared = self.cfg["cleared"].get(uid, {})
            unread, recent = {}, {}
            for m in self.messages:
                if uid not in (m["frm"], m["to"]):
                    continue
                if m["n"] <= cleared.get(m["to"] if m["frm"] == uid else m["frm"], 0):
                    continue
                if m["to"] == uid:
                    o = m["frm"]
                    recent[o] = m.get("frm_name")
                    if m["n"] > reads.get(o, 0):
                        unread[o] = unread.get(o, 0) + 1
                elif m["frm"] == uid:
                    recent[m["to"]] = m.get("to_name")
            for o, name in recent.items():
                if o not in users and o != uid:
                    users[o] = {"uid": o, "name": name or "?", "status": "online", "note": "",
                                "kind": "mobile" if ":" in o else "pc", "online": False}
            for u in users.values():
                u["unread"] = unread.get(u["uid"], 0)
            return sorted(users.values(), key=lambda u: (not u["online"], u["name"].lower()))

    def state_for(self, uid):
        return {"t": "state", "me": self.user_info(uid), "contacts": self.contacts_for(uid)}

    def uid_for_token(self, token, ip):
        if not token:
            return None
        if token == self.desk_token and ip in ("127.0.0.1", "::1", "::ffff:127.0.0.1"):
            return self.node_id
        return self.tokens.get(token)

    def register_web(self, name):
        with self.lock:
            token = secrets.token_hex(16)
            uid = "%s:%s" % (self.node_id, secrets.token_hex(4))
            self.cfg["web"][token] = {"uid": uid, "name": (name or "Phone").strip()[:30] or "Phone",
                                      "status": "online", "note": "", "seen": time.time()}
            self.tokens[token] = uid
            self._save_cfg()
            self._bump(beacon=True)
            return token, uid

    def update_profile(self, uid, data):
        with self.lock:
            prof = self.cfg["desk"] if uid == self.node_id else self._web_entry(uid)
            if prof is None:
                return
            if "name" in data and str(data["name"]).strip():
                prof["name"] = str(data["name"]).strip()[:30]
            if data.get("status") in STATUSES:
                prof["status"] = data["status"]
            if data.get("lang") in ("auto", "ko", "en"):
                prof["lang"] = "ko" if data["lang"] == "ko" else "en"
            if "note" in data:
                prof["note"] = str(data["note"] or "").strip()[:60]
            self._save_cfg()
            self._bump(beacon=True)

    def mark_read(self, uid, peer):
        with self.lock:
            n = 0
            for m in reversed(self.messages):
                if m["frm"] == peer and m["to"] == uid:
                    n = m["n"]
                    break
            r = self.cfg["reads"].setdefault(uid, {})
            if n and r.get(peer, 0) < n:
                r[peer] = n
                self._save_cfg()
                self._bump()

    def history(self, uid, peer):
        with self.lock:
            cut = self._cut(uid, peer)
            out = [m for m in self.messages
                   if m["n"] > cut and ((m["frm"] == uid and m["to"] == peer) or (m["frm"] == peer and m["to"] == uid))]
            return out[-HISTORY_LIMIT:]

    def clear_chat(self, uid, peer):
        """uid의 화면에서 peer와의 대화를 삭제. 이 PC에 기록된 모든 당사자가 지운 메시지는 파일에서도 제거."""
        with self.lock:
            cut = 0
            for m in self.messages:
                if {m["frm"], m["to"]} == {uid, peer}:
                    cut = max(cut, m["n"])
            if not cut:
                return
            self.cfg["cleared"].setdefault(uid, {})[peer] = cut
            self.cfg["reads"].setdefault(uid, {})[peer] = max(self.cfg["reads"].get(uid, {}).get(peer, 0), cut)
            keep, removed = [], []
            for m in self.messages:
                locals_ = [p for p in (m["frm"], m["to"]) if node_of(p) == self.node_id]
                gone = m.get("st") != "pending" and locals_ and all(
                    self._cut(p, m["to"] if p == m["frm"] else m["frm"]) >= m["n"] for p in locals_)
                (removed if gone else keep).append(m)
            if removed:
                self.messages = keep
                for m in removed:
                    self.by_mid.pop(m["mid"], None)
                    if m.get("type") == "file":
                        meta = self.files.pop(m["fid"], None)
                        self.findex.pop(m["fid"], None)
                        cache = os.path.join(self.files_dir, m["fid"])
                        if os.path.isdir(cache):          # 임시 보관 파일만 삭제 (문서 폴더 파일은 유지)
                            shutil.rmtree(cache, ignore_errors=True)
                self._rewrite_log()
                self._set_file_index()
            self._save_cfg()
            data = json.dumps({"t": "cleared", "peer": peer}, ensure_ascii=False)
            for s in list(self.subs):
                if s.uid == uid:
                    s.q.put(data)
            self._bump()

    def _set_file_index(self):
        tmp = self.findex_path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(self.findex, f, ensure_ascii=False)
        os.replace(tmp, self.findex_path)

    def client_connected(self, sub, delta):
        with self.lock:
            if delta > 0:
                self.subs.add(sub)
            else:
                self.subs.discard(sub)
            if sub.uid != self.node_id:
                before = self.online_web.get(sub.uid, 0)
                after = max(0, before + delta)
                self.online_web[sub.uid] = after
                w = self._web_entry(sub.uid)
                if w is not None:
                    w["seen"] = time.time()
                if (before == 0) != (after == 0):
                    self._save_cfg()
                    self._bump(beacon=True)

    def _bump(self, beacon=False):
        self.version += 1
        if beacon:
            self.beacon_now.set()
        self.wake.set()

    # ------------------------------------------------------------ messages
    def _store(self, m):
        with self.lock:
            if m["mid"] in self.by_mid:
                return self.by_mid[m["mid"]]
            self.seq += 1
            m["n"] = self.seq
            self.messages.append(m)
            self.by_mid[m["mid"]] = m
            if m.get("st") == "pending":
                self.pending[m["mid"]] = m
            if m.get("type") == "file":
                self._index_file(m)
            self._append_log(m)
            self._push_msg(m)
            self._bump()
            return m

    def _set_status(self, m, st):
        with self.lock:
            m["st"] = st
            if st != "pending":
                self.pending.pop(m["mid"], None)
            self._append_log(m)
            self._push_msg(m)

    def _push_msg(self, m):
        data = json.dumps({"t": "msg", "m": m}, ensure_ascii=False)
        for s in list(self.subs):
            if s.uid in (m["frm"], m["to"]):
                s.q.put(data)

    def _new_msg(self, frm, to, **kw):
        m = {"mid": uuid.uuid4().hex, "frm": frm, "to": to,
             "frm_name": self.display_name(frm), "to_name": self.display_name(to),
             "ts": int(time.time() * 1000)}
        m.update(kw)
        return m

    def _route(self, m):
        local = node_of(m["to"]) == self.node_id
        m["st"] = "sent" if local else "pending"
        m = self._store(m)
        if local:
            self._fire_incoming(m)
        else:
            self._kick_outbox()
        return m

    def send_text(self, uid, peer, text):
        return self._route(self._new_msg(uid, peer, type="text", text=text[:MAX_TEXT]))

    def add_file(self, uid, peer, fid, fname, size, path):
        if peer == self.node_id:   # 같은 PC의 폰 → 이 PC: 받은 파일 폴더로
            try:
                path = self._to_recv_dir(path, fname)
                shutil.rmtree(os.path.join(self.files_dir, fid), ignore_errors=True)
            except OSError:
                log.exception("move to recv dir")
        self._set_file_path(fid, path)
        mime = mimetypes.guess_type(fname)[0] or "application/octet-stream"
        return self._route(self._new_msg(uid, peer, type="file", fid=fid, fname=fname, size=size, mime=mime))

    def _fire_incoming(self, m):
        cb = self.on_incoming
        if cb:
            try:
                cb(m)
            except Exception:
                log.exception("on_incoming")

    # ------------------------------------------------------------ outbox (p2p send)
    def _kick_outbox(self):
        now = time.time()
        with self.lock:
            todo = [m for m in self.pending.values()
                    if m["mid"] not in self.inflight
                    and self.retry_at.get(m["mid"], 0) <= now
                    and node_of(m["to"]) in self.peers]
            for m in todo:
                self.inflight.add(m["mid"])
        for m in todo:
            threading.Thread(target=self._deliver, args=(m,), daemon=True).start()

    def _deliver(self, m):
        try:
            with self.lock:
                p = self.peers.get(node_of(m["to"]))
                if not p:
                    return
                url = "http://%s:%d/p2p/msg" % (p["ip"], p["port"])
            body = {k: m[k] for k in MSG_FIELDS if k in m}
            body["port"] = self.port
            body["node"] = self.node_id
            req = urllib.request.Request(url, data=json.dumps(body, ensure_ascii=False).encode("utf-8"),
                                         headers={"Content-Type": "application/json"})
            timeout = 20 if m.get("type") == "text" else 3600
            with NO_PROXY.open(req, timeout=timeout) as r:
                r.read()
            self._set_status(m, "sent")
        except urllib.error.HTTPError as e:
            if e.code in (400, 404):
                log.warning("deliver %s rejected: %s", m["mid"], e.code)
                self._set_status(m, "failed")
            else:
                self.retry_at[m["mid"]] = time.time() + 3
        except Exception as e:
            log.info("deliver %s later: %s", m["mid"], e)
            self.retry_at[m["mid"]] = time.time() + 3
        finally:
            with self.lock:
                self.inflight.discard(m["mid"])

    def p2p_receive(self, data, ip):
        """return http status"""
        mid = str(data.get("mid", ""))[:40]
        to = str(data.get("to", ""))
        frm = str(data.get("frm", ""))
        if not re.match(r"^[0-9a-f]{8,40}$", mid) or not frm or node_of(frm) == self.node_id:
            return 400
        with self.lock:
            if mid in self.by_mid:
                return 200
            if to not in self._local_uids():
                return 404
        m = {"mid": mid, "frm": frm, "to": to,
             "frm_name": str(data.get("frm_name", "") or "?")[:30],
             "to_name": str(data.get("to_name", "") or "")[:30],
             "ts": int(time.time() * 1000), "st": "recv"}
        if data.get("type") == "file":
            fid = str(data.get("fid", ""))
            if not FID_RE.match(fid):
                return 400
            fname = safe_fname(data.get("fname"))
            try:
                size = int(data.get("size", 0))
                port = int(data.get("port", 0))
            except (TypeError, ValueError):
                return 400
            old = self.findex.get(fid)
            if not (old and os.path.exists(old) and os.path.getsize(old) == size):
                fdir = os.path.join(self.files_dir, fid)
                os.makedirs(fdir, exist_ok=True)
                part = os.path.join(fdir, fname + ".part")
                try:
                    url = "http://%s:%d/p2p/file/%s" % (ip, port, fid)
                    with NO_PROXY.open(url, timeout=60) as r, open(part, "wb") as f:
                        shutil.copyfileobj(r, f, 256 * 1024)
                    if os.path.getsize(part) != size:
                        raise IOError("size mismatch")
                    if to == self.node_id:
                        final = self._to_recv_dir(part, fname)
                        shutil.rmtree(fdir, ignore_errors=True)
                    else:
                        final = os.path.join(fdir, fname)
                        os.replace(part, final)
                    self._set_file_path(fid, final)
                except Exception as e:
                    log.warning("file download failed: %s", e)
                    shutil.rmtree(fdir, ignore_errors=True)
                    return 502
            m.update(type="file", fid=fid, fname=fname, size=size,
                     mime=mimetypes.guess_type(fname)[0] or "application/octet-stream")
        else:
            text = str(data.get("text", ""))[:MAX_TEXT]
            if not text:
                return 400
            m.update(type="text", text=text)
        with self.lock:
            if mid in self.by_mid:
                return 200
            self._store(m)
        self._fire_incoming(m)
        return 200

    # ------------------------------------------------------------ discovery
    def _beacon_payload(self, bye=False):
        with self.lock:
            p = {"app": APP, "v": PROTO, "node": self.node_id, "port": self.port, "udp": self.udp_port}
            if bye:
                p["bye"] = True
            else:
                p["users"] = self._local_users()
        return json.dumps(p, ensure_ascii=False).encode("utf-8")

    def _targets(self):
        t = [("255.255.255.255", self.udp_port)]
        for ip in lan_ips():
            parts = ip.split(".")
            t.append((".".join(parts[:3] + ["255"]), self.udp_port))
        t.extend(self.extra_peers)
        return t

    def _send_beacon(self, targets=None, bye=False):
        data = self._beacon_payload(bye)
        for addr in (targets or self._targets()):
            try:
                self.udp.sendto(data, addr)
            except OSError:
                pass

    def _udp_loop(self):
        while self.running:
            try:
                data, addr = self.udp.recvfrom(65535)
            except OSError:
                if not self.running:
                    break
                time.sleep(0.2)
                continue
            try:
                p = json.loads(data.decode("utf-8"))
                if p.get("app") != APP or p.get("node") == self.node_id:
                    continue
                nid = str(p["node"])[:40]
                port = int(p["port"])
            except (ValueError, KeyError, TypeError, UnicodeDecodeError):
                continue
            new = False
            with self.lock:
                if p.get("bye"):
                    if self.peers.pop(nid, None):
                        self._bump()
                    continue
                users = [u for u in (clean_user(x, nid) for x in p.get("users", [])) if u]
                old = self.peers.get(nid)
                self.peers[nid] = {"ip": addr[0], "port": port, "users": users, "seen": time.time()}
                if not old or old["users"] != users or old["ip"] != addr[0] or old["port"] != port:
                    self._bump()
                new = old is None
            if new:
                try:
                    reply_port = int(p.get("udp", self.udp_port))
                except (TypeError, ValueError):
                    reply_port = self.udp_port
                self._send_beacon([(addr[0], reply_port)])
                self._kick_outbox()

    def _tick_loop(self):
        last_beacon = 0
        while self.running:
            now = time.time()
            with self.lock:
                dead = [n for n, p in self.peers.items() if now - p["seen"] > PEER_TIMEOUT]
                for n in dead:
                    del self.peers[n]
                if dead:
                    self._bump()
            if self.beacon_now.is_set() or now - last_beacon >= BEACON_INTERVAL:
                self.beacon_now.clear()
                self._send_beacon()
                last_beacon = now
            self._kick_outbox()
            self._push_states()
            self.wake.wait(0.5)
            self.wake.clear()

    def _push_states(self):
        with self.lock:
            if self.version == self.pushed_version:
                return
            self.pushed_version = self.version
            subs = list(self.subs)
        cache = {}
        for s in subs:
            if s.uid not in cache:
                cache[s.uid] = json.dumps(self.state_for(s.uid), ensure_ascii=False)
            data = cache[s.uid]
            if data != s.last:
                s.last = data
                s.q.put(data)

    # ------------------------------------------------------------ lifecycle
    def start(self):
        last_err = None
        for port in range(self.want_port, self.want_port + 20):
            try:
                self.httpd = LanHTTPServer(("0.0.0.0", port), Handler)
                break
            except OSError as e:
                last_err = e
        else:
            raise last_err
        self.httpd.node = self
        self.port = self.httpd.server_address[1]

        self.udp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.udp.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.udp.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        self.udp.bind(("", self.udp_port))

        self.running = True
        for target in (self.httpd.serve_forever, self._udp_loop, self._tick_loop):
            threading.Thread(target=target, daemon=True).start()
        log.info("node %s on http %d / udp %d", self.node_id, self.port, self.udp_port)

    def stop(self):
        if not self.running:
            return
        try:
            self._send_beacon(bye=True)
        except Exception:
            pass
        self.running = False
        try:
            self.udp.close()
        except Exception:
            pass

    def desk_korean(self):
        return self.cfg["desk"].get("lang") == "ko"

    def desk_url(self, **q):
        q["t"] = self.desk_token
        return "http://127.0.0.1:%d/?%s" % (self.port, urlencode(q))

    def phone_urls(self):
        return ["http://%s:%d/" % (ip, self.port) for ip in lan_ips()]


class LanHTTPServer(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = os.name != "nt"   # Windows에서는 포트 중복 바인딩 방지


# ====================================================================== http
class Handler(BaseHTTPRequestHandler):
    server_version = "LANChat/2"
    protocol_version = "HTTP/1.0"

    def log_message(self, fmt, *args):
        pass

    @property
    def node(self):
        return self.server.node

    def _send(self, status, body, ctype, extra=None):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, status=200, extra=None):
        self._send(status, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                   "application/json; charset=utf-8", extra)

    def _err(self, status, text):
        self._json({"error": text}, status)

    def _token(self, qs):
        t = self.headers.get("X-Token") or qs.get("t", [""])[0]
        if not t:
            mm = re.search(r"(?:^|;\s*)lct=([0-9a-f]{32})", self.headers.get("Cookie", ""))
            t = mm.group(1) if mm else ""
        return t

    def _auth(self, qs):
        uid = self.node.uid_for_token(self._token(qs), self.client_address[0])
        if not uid:
            self._err(401, "Login required")
        return uid

    def _body_json(self, limit=1024 * 1024):
        try:
            n = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            n = 0
        if n <= 0 or n > limit:
            return None
        try:
            d = json.loads(self.rfile.read(n).decode("utf-8"))
            return d if isinstance(d, dict) else None
        except (ValueError, UnicodeDecodeError):
            return None

    # ---------------------------------------------------------------- GET
    def do_GET(self):
        url = urlparse(self.path)
        qs = parse_qs(url.query)
        path = url.path
        try:
            if path == "/":
                self._send(200, PAGE.replace("__MAX_UPLOAD__", str(MAX_UPLOAD)).encode("utf-8"),
                           "text/html; charset=utf-8")
            elif path == "/api/init":
                uid = self._auth(qs)
                if uid:
                    st = self.node.state_for(uid)
                    self._json({"me": st["me"], "contacts": st["contacts"], "urls": self.node.phone_urls(),
                                "native": self.node.native and uid == self.node.node_id,
                                "desk": uid == self.node.node_id})
            elif path == "/api/history":
                uid = self._auth(qs)
                if uid:
                    peer = qs.get("peer", [""])[0]
                    self._json({"peer": self.node.user_info(peer), "messages": self.node.history(uid, peer)})
            elif path == "/api/events":
                uid = self._auth(qs)
                if uid:
                    self._events(uid)
            elif path == "/api/qr":
                self._qr(qs.get("u", [""])[0])
            elif path.startswith("/files/"):
                self._file(path[7:], download="dl" in qs)
            elif path.startswith("/p2p/file/"):
                self._file(path[10:], download=True)
            elif path in ("/icon.png", "/favicon.ico"):
                self._send(200, ICON_PNG, "image/png", {"Cache-Control": "max-age=86400"})
            elif path == "/manifest.webmanifest":
                self._send(200, MANIFEST.encode("utf-8"), "application/manifest+json")
            else:
                self._err(404, "not found")
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass

    def _events(self, uid):
        node = self.node
        sub = Sub(uid)
        first = json.dumps(node.state_for(uid), ensure_ascii=False)
        sub.last = first
        node.client_connected(sub, +1)
        try:
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream; charset=utf-8")
            self.send_header("Cache-Control", "no-cache")
            self.end_headers()
            self.wfile.write(("retry: 2000\ndata: %s\n\n" % first).encode("utf-8"))
            self.wfile.flush()
            while node.running:
                try:
                    data = "data: %s\n\n" % sub.q.get(timeout=15)
                except queue.Empty:
                    data = ": ping\n\n"
                self.wfile.write(data.encode("utf-8"))
                self.wfile.flush()
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
            pass
        finally:
            node.client_connected(sub, -1)

    def _qr(self, text):
        try:
            import segno
        except ImportError:
            return self._err(404, "segno not installed")
        buf = io.BytesIO()
        segno.make(text[:500], error="m").save(buf, kind="svg", scale=6, border=2, dark="#000", light="#fff")
        self._send(200, buf.getvalue(), "image/svg+xml")

    def _file(self, fid, download):
        if not FID_RE.match(fid):
            return self._err(404, "not found")
        with self.node.lock:
            meta = self.node.files.get(fid)
        if not meta or not os.path.exists(meta["path"]):
            return self._err(404, "not found")
        mime = meta.get("mime") or "application/octet-stream"
        inline_ok = ((mime.startswith(("image/", "video/", "audio/")) and mime != "image/svg+xml")
                     or mime == "application/pdf")
        disp = "inline" if (inline_ok and not download) else "attachment"
        size = os.path.getsize(meta["path"])
        self.send_response(200)
        self.send_header("Content-Type", mime)
        self.send_header("Content-Length", str(size))
        self.send_header("Content-Disposition", "%s; filename*=UTF-8''%s" % (disp, quote(meta["fname"])))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", "sandbox")
        self.send_header("Cache-Control", "private, max-age=86400")
        self.end_headers()
        with open(meta["path"], "rb") as f:
            shutil.copyfileobj(f, self.wfile, 256 * 1024)

    # ---------------------------------------------------------------- POST
    def do_POST(self):
        url = urlparse(self.path)
        qs = parse_qs(url.query)
        path = url.path
        node = self.node
        try:
            if path == "/p2p/msg":
                data = self._body_json()
                if data is None:
                    return self._err(400, "bad request")
                st = node.p2p_receive(data, self.client_address[0])
                return self._json({"ok": st == 200}, st)

            if path == "/api/register":
                data = self._body_json() or {}
                token, uid = node.register_web(str(data.get("name", "")))
                return self._json({"uid": uid}, extra={
                    "Set-Cookie": "lct=%s; Max-Age=315360000; Path=/; SameSite=Lax; HttpOnly" % token})

            uid = self._auth(qs)
            if not uid:
                return
            if path == "/api/send":
                data = self._body_json()
                if not data or not str(data.get("text", "")).strip() or not data.get("peer"):
                    return self._err(400, "Empty message")
                peer = str(data["peer"])[:80]
                if peer == uid:
                    return self._err(400, "Invalid recipient")
                self._json(node.send_text(uid, peer, str(data["text"])))
            elif path == "/api/upload":
                self._upload(uid, qs.get("peer", [""])[0][:80])
            elif path == "/api/profile":
                node.update_profile(uid, self._body_json() or {})
                self._json({"ok": True})
            elif path == "/api/clear":
                data = self._body_json() or {}
                node.clear_chat(uid, str(data.get("peer", ""))[:80])
                self._json({"ok": True})
            elif path == "/api/read":
                data = self._body_json() or {}
                node.mark_read(uid, str(data.get("peer", "")))
                self._json({"ok": True})
            else:
                self._err(404, "not found")
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass

    def _upload(self, uid, peer):
        if not peer or peer == uid:
            return self._err(400, "Invalid recipient")
        try:
            length = int(self.headers.get("Content-Length", "-1"))
        except ValueError:
            length = -1
        if length < 0:
            return self._err(411, "Content-Length required")
        if length > MAX_UPLOAD:
            return self._err(413, "File too large")
        from urllib.parse import unquote
        fname = safe_fname(unquote(self.headers.get("X-Filename", "") or "file"))
        fid = uuid.uuid4().hex
        fdir = os.path.join(self.node.files_dir, fid)
        os.makedirs(fdir, exist_ok=True)
        final = os.path.join(fdir, fname)
        part = final + ".part"
        remaining = length
        try:
            with open(part, "wb") as f:
                while remaining > 0:
                    chunk = self.rfile.read(min(256 * 1024, remaining))
                    if not chunk:
                        break
                    f.write(chunk)
                    remaining -= len(chunk)
        except OSError:
            remaining = 1
        if remaining > 0:
            shutil.rmtree(fdir, ignore_errors=True)
            return self._err(400, "Upload interrupted")
        os.replace(part, final)
        self._json(self.node.add_file(uid, peer, fid, fname, length, final))


# ====================================================================== desktop
def run_detached(cmd):
    """콘솔 없는 exe(--windowed)에서도 동작하도록 입출력을 모두 닫고 실행"""
    kw = {"stdin": subprocess.DEVNULL, "stdout": subprocess.DEVNULL, "stderr": subprocess.DEVNULL, "close_fds": True}
    if os.name == "nt":
        kw["creationflags"] = 0x08000000   # CREATE_NO_WINDOW
    return subprocess.Popen(cmd, **kw)


def reveal_in_explorer(path):
    """탐색기에서 파일이 있는 폴더를 열고 그 파일을 선택"""
    try:
        import ctypes
        from ctypes import wintypes
        shell32, ole32 = ctypes.windll.shell32, ctypes.windll.ole32
        ole32.CoInitialize(None)
        shell32.SHParseDisplayName.argtypes = [wintypes.LPCWSTR, ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p),
                                               wintypes.ULONG, ctypes.POINTER(wintypes.ULONG)]
        shell32.SHOpenFolderAndSelectItems.argtypes = [ctypes.c_void_p, wintypes.UINT, ctypes.c_void_p, wintypes.DWORD]
        ole32.CoTaskMemFree.argtypes = [ctypes.c_void_p]
        pidl = ctypes.c_void_p()
        if shell32.SHParseDisplayName(path, None, ctypes.byref(pidl), 0, None) != 0:
            raise OSError("SHParseDisplayName failed")
        try:
            if shell32.SHOpenFolderAndSelectItems(pidl, 0, None, 0) != 0:
                raise OSError("SHOpenFolderAndSelectItems failed")
        finally:
            ole32.CoTaskMemFree(pidl)
    except Exception:
        log.exception("reveal via shell API failed, falling back to explorer")
        run_detached(["explorer", "/select,", path])


class DeskApi:
    """JS에서 window.pywebview.api.* 로 호출"""

    def __init__(self, app):
        self._app = app

    def open_chat(self, peer):
        self._app.open_chat(str(peer), focus=True)

    def open_file(self, fid):
        self._app.open_file(str(fid), reveal=False)

    def show_file(self, fid):
        self._app.open_file(str(fid), reveal=True)

    def open_recv_dir(self):
        self._app.open_recv_dir()

    def toast_open(self, peer):
        self._app.toast_open(str(peer))

    def toast_close(self):
        self._app.close_toast()


class DesktopApp:
    def __init__(self, node, start_hidden=False):
        self.node = node
        self.wins = {}
        self.wlock = threading.Lock()
        self.main = None
        self.webview = None
        self.tray = None
        self.start_hidden = start_hidden
        self.quitting = False
        self.toast = None
        self.toast_lock = threading.Lock()
        self.unread = 0

    def t(self, ko, en):
        return ko if self.node.desk_korean() else en

    def run(self):
        import webview
        self.webview = webview
        try:
            webview.settings["ALLOW_DOWNLOADS"] = True
        except Exception:
            pass
        self.api = DeskApi(self)
        self._start_tray()
        hidden = self.start_hidden and self.tray is not None
        self.main = self._create("LAN Chat", self.node.desk_url(view="list"),
                                 width=340, height=620, min_size=(280, 420), hidden=hidden)
        if self.tray is not None:
            self.main.events.closing += self._main_closing   # 닫기 → 트레이로 숨김
        self.main.events.closed += self.quit
        self.node.on_incoming = self._incoming
        self.node.native = True
        threading.Thread(target=self._unread_loop, daemon=True).start()
        webview.start()
        self.quit()

    # ---------------------------------------------------------- tray (백그라운드 실행)
    def _start_tray(self):
        try:
            import pystray
            from PIL import Image
        except Exception:
            log.warning("pystray/Pillow 없음 → 창을 닫으면 종료됩니다")
            return
        image = Image.open(io.BytesIO(ICON_PNG))
        menu = pystray.Menu(
            pystray.MenuItem(lambda item: self.t("LAN Chat 열기", "Open LAN Chat"),
                             lambda icon, item: self.show_main(), default=True),
            pystray.MenuItem(lambda item: self.t("받은 파일 폴더", "Received files"),
                             lambda icon, item: self.open_recv_dir()),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem(lambda item: self.t("종료", "Quit"), lambda icon, item: self.quit()),
        )
        self.tray = pystray.Icon("LANChat", image, "LAN Chat", menu)
        threading.Thread(target=self.tray.run, daemon=True).start()

    def _notify(self, text):
        if self.tray is not None:
            try:
                self.tray.notify(text[:200], "LAN Chat")
            except Exception:
                pass

    def _main_closing(self):
        if self.quitting or self._windows_shutting_down():
            self.quitting = True
            return True
        threading.Thread(target=self._hide_main, daemon=True).start()
        return False   # 창 닫기 취소 → 대신 숨김

    @staticmethod
    def _windows_shutting_down():
        try:
            import ctypes
            return bool(ctypes.windll.user32.GetSystemMetrics(0x2000))  # SM_SHUTTINGDOWN
        except Exception:
            return False

    def _hide_main(self):
        try:
            self.main.hide()
        except Exception:
            pass
        if not self.node.cfg.get("tray_hint"):
            self.node.cfg["tray_hint"] = True
            self.node._save_cfg()
            self._notify(self.t("LAN Chat은 트레이에서 계속 실행 중입니다. 종료하려면 트레이 아이콘을 오른쪽 클릭하세요.",
                                "LAN Chat is still running in the tray. Right-click the tray icon to quit."))

    def quit(self):
        self.quitting = True
        try:
            self.node.stop()
        except Exception:
            pass
        if self.tray is not None:
            try:
                self.tray.stop()
            except Exception:
                pass
        os._exit(0)

    def show_main(self):
        if self.main:
            self._front(self.main)

    def _front(self, w):
        for fn in (w.restore, w.show):
            try:
                fn()
            except Exception:
                pass
        try:
            w.on_top = True
            w.on_top = False
        except Exception:
            pass

    def _create(self, title, url, **kw):
        kw.setdefault("text_select", True)   # 드래그로 텍스트 선택/복사 허용
        try:
            return self.webview.create_window(title, url, js_api=self.api, **kw)
        except TypeError:
            for k in ("focus", "text_select", "hidden"):
                kw.pop(k, None)
            return self.webview.create_window(title, url, js_api=self.api, **kw)

    def open_chat(self, peer, focus=True):
        with self.wlock:
            w = self.wins.get(peer)
            if w is None:
                title = "%s - %s" % (self.node.display_name(peer), ("대화" if self.node.desk_korean() else "Chat"))
                w = self._create(title, self.node.desk_url(view="chat", peer=peer),
                                 width=480, height=620, min_size=(320, 360), focus=focus)
                self.wins[peer] = w

                def closed(p=peer, ww=w):
                    with self.wlock:
                        if self.wins.get(p) is ww:
                            del self.wins[p]
                w.events.closed += lambda: closed()
                return
        if focus:
            self._front(w)

    def _incoming(self, m):
        """새 메시지: 대화창을 띄우지 않고 오른쪽 아래 알림 팝업 + 알림음 (카카오톡 방식)"""
        if m.get("to") != self.node.node_id:
            return
        if self.node.cfg["desk"].get("status") == "busy":   # 다른 용무 중 = 알림 끔
            return
        with self.wlock:
            chat_open = m["frm"] in self.wins
        try:
            import winsound
            winsound.PlaySound("SystemNotification", winsound.SND_ALIAS | winsound.SND_ASYNC)
        except Exception:
            pass
        if not chat_open:
            threading.Thread(target=self.show_toast, args=(m,), daemon=True).start()

    # ---------------------------------------------------------- 알림 팝업
    def _toast_geometry(self, w, h):
        try:
            scr = self.webview.screens[0]
            sx, sy, sw, sh = scr.x, scr.y, scr.width, scr.height
        except Exception:
            sx, sy, sw, sh = 0, 0, 1280, 720
        right, bottom = sx + sw, sy + sh - 48
        try:
            import ctypes
            from ctypes import wintypes
            rect = wintypes.RECT()
            ctypes.windll.user32.SystemParametersInfoW(0x30, 0, ctypes.byref(rect), 0)   # SPI_GETWORKAREA
            cx = ctypes.windll.user32.GetSystemMetrics(0)
            cy = ctypes.windll.user32.GetSystemMetrics(1)
            if cx and cy:   # 작업 영역을 화면 비율로 환산 (DPI 단위 차이와 무관)
                right = sx + sw * rect.right / cx
                bottom = sy + sh * rect.bottom / cy
        except Exception:
            pass
        return int(right - w - 12), int(bottom - h - 12)

    def show_toast(self, m):
        import html as H
        name = m.get("frm_name") or "?"
        body = m.get("text") if m.get("type") == "text" else "📎 " + str(m.get("fname", ""))
        hue = 0
        for ch in m["frm"]:
            hue = (hue * 31 + ord(ch)) & 0xFFFFFFFF
        hue %= 360
        page = TOAST_HTML.replace("__NAME__", H.escape(name)).replace("__BODY__", H.escape(body or "")) \
            .replace("__INITIAL__", H.escape(name.strip()[:1].upper() or "?")).replace("__HUE__", str(hue)) \
            .replace("__PEER__", json.dumps(m["frm"])).replace("__APP__", "LAN Chat")
        w, h = 340, 96
        x, y = self._toast_geometry(w, h)
        with self.toast_lock:
            old, self.toast = self.toast, None
            if old is not None:
                try:
                    old.destroy()
                except Exception:
                    pass
            try:
                self.toast = self.webview.create_window(
                    "LAN Chat", html=page, js_api=self.api, width=w, height=h, x=x, y=y,
                    frameless=True, on_top=True, focus=False, resizable=False, text_select=False)
            except TypeError:
                self.toast = self.webview.create_window(
                    "LAN Chat", html=page, js_api=self.api, width=w, height=h, x=x, y=y,
                    frameless=True, on_top=True, resizable=False)

    def close_toast(self):
        with self.toast_lock:
            t, self.toast = self.toast, None
        if t is not None:
            try:
                t.destroy()
            except Exception:
                pass

    def toast_open(self, peer):
        self.close_toast()
        self.open_chat(peer, focus=True)

    # ---------------------------------------------------------- 안 읽은 메시지 표시 (트레이)
    def _unread_loop(self):
        while True:
            try:
                n = sum(c.get("unread", 0) for c in self.node.contacts_for(self.node.node_id))
                if n != self.unread:
                    self.unread = n
                    self._update_badge(n)
            except Exception:
                log.exception("unread")
            time.sleep(1)

    def _update_badge(self, n):
        title = "LAN Chat" + (" (%d)" % n if n else "")
        try:
            if self.main:
                self.main.set_title(title)
        except Exception:
            pass
        if self.tray is None:
            return
        try:
            from PIL import Image, ImageDraw
            img = Image.open(io.BytesIO(ICON_PNG)).convert("RGBA").resize((64, 64))
            if n:
                d = ImageDraw.Draw(img)
                d.ellipse([34, 0, 63, 29], fill=(235, 64, 52, 255), outline=(255, 255, 255, 255), width=3)
            self.tray.icon = img
            self.tray.title = title
        except Exception:
            log.exception("badge")

    def open_recv_dir(self):
        d = self.node.recv_dir
        os.makedirs(d, exist_ok=True)
        try:
            if os.name == "nt":
                os.startfile(d)
            else:
                run_detached(["open" if sys.platform == "darwin" else "xdg-open", d])
        except Exception:
            log.exception("open_recv_dir")

    def open_file(self, fid, reveal):
        meta = self.node.files.get(fid)
        if not meta or not os.path.exists(meta["path"]):
            return
        path = os.path.normpath(meta["path"])
        try:
            if os.name == "nt":
                if reveal:
                    reveal_in_explorer(path)
                else:
                    os.startfile(path)
            elif sys.platform == "darwin":
                run_detached(["open", "-R", path] if reveal else ["open", path])
            else:
                run_detached(["xdg-open", os.path.dirname(path) if reveal else path])
        except Exception:
            log.exception("open_file")


# ====================================================================== single instance
def acquire_lock(port):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    if os.name == "nt" and hasattr(socket, "SO_EXCLUSIVEADDRUSE"):
        s.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
    try:
        s.bind(("127.0.0.1", port))
        s.listen(4)
        return s
    except OSError:
        s.close()
        return None


def poke_existing(port):
    try:
        with socket.create_connection(("127.0.0.1", port), timeout=2) as c:
            c.sendall(b"show")
        return True
    except OSError:
        return False


def lock_listener(sock, on_show):
    while True:
        try:
            c, _ = sock.accept()
            with c:
                c.settimeout(2)
                if c.recv(16).startswith(b"show"):
                    on_show()
        except OSError:
            time.sleep(0.5)


def message_box(text):
    try:
        import ctypes
        ctypes.windll.user32.MessageBoxW(None, text, "LAN Chat", 0x40)
    except Exception:
        print(text)


# ====================================================================== main
def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="LAN Chat")
    ap.add_argument("--port", type=int, default=8000)
    ap.add_argument("--data", default=None, help="데이터 폴더 (기본: %%APPDATA%%\\LANChat)")
    ap.add_argument("--browser", action="store_true", help="창 대신 기본 브라우저 사용")
    ap.add_argument("--server", action="store_true", help="창 없이 실행")
    ap.add_argument("--name", default=None)
    ap.add_argument("--recv-dir", default=None, help="받은 파일 폴더 (기본: 문서\\LAN Chat)")
    ap.add_argument("--udp-port", type=int, default=UDP_PORT)
    ap.add_argument("--peer", action="append", default=[], help="브로드캐스트가 막힌 망에서 직접 지정: IP[:UDP포트]")
    ap.add_argument("--lock-port", type=int, default=LOCK_PORT)
    ap.add_argument("--minimized", action="store_true", help="트레이에 숨긴 상태로 시작 (자동 실행용)")
    args = ap.parse_args()

    data_dir = args.data or default_data_dir()
    os.makedirs(data_dir, exist_ok=True)
    handlers = [logging.FileHandler(os.path.join(data_dir, "lanchat.log"), encoding="utf-8")]
    if sys.stdout is not None:
        handlers.append(logging.StreamHandler(sys.stdout))
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s", handlers=handlers)

    if os.name == "nt":
        try:
            import ctypes
            global _MUTEX
            _MUTEX = ctypes.windll.kernel32.CreateMutexW(None, False, "LANChat_SingleInstance_Mutex")
        except Exception:
            pass

    lock = None
    if not args.server:
        lock = acquire_lock(args.lock_port)
        if lock is None:
            if not poke_existing(args.lock_port):
                message_box(tr("LAN Chat이 이미 실행 중입니다.", "LAN Chat is already running."))
            return

    peers = []
    for p in args.peer:
        host, _, port = p.partition(":")
        peers.append((host, int(port) if port else args.udp_port))

    node = Node(data_dir, args.port, args.udp_port, peers, args.name, args.recv_dir)
    try:
        node.start()
    except OSError as e:
        message_box(tr("네트워크 포트를 열 수 없습니다: %s", "Could not open network port: %s") % e)
        return

    print("=" * 50)
    print(" LAN Chat running  (name: %s)" % node.cfg["desk"]["name"])
    for u in node.phone_urls():
        print(" Phone URL:     %s" % u)
    print(" Data folder:   %s" % data_dir)
    print(" Received:      %s" % node.recv_dir)
    if args.server:
        print(" Desktop UI:    %s" % node.desk_url(view="list"))
    print("=" * 50)

    use_window = not (args.server or args.browser)
    if use_window:
        try:
            import webview  # noqa: F401
        except Exception:
            log.warning("pywebview not available -> browser mode")
            use_window = False

    if use_window:
        app = DesktopApp(node, start_hidden=args.minimized)
        threading.Thread(target=lock_listener, args=(lock, app.show_main), daemon=True).start()
        app.run()
        return

    if not args.server:
        opener = lambda: webbrowser.open(node.desk_url(view="list"))
        threading.Thread(target=lock_listener, args=(lock, opener), daemon=True).start()
        opener()
    try:
        while True:
            time.sleep(3600)
    except KeyboardInterrupt:
        pass
    finally:
        node.stop()


# ====================================================================== assets
ICON_PNG = __import__("base64").b64decode(
    "iVBORw0KGgoAAAANSUhEUgAAAMAAAADACAYAAABS3GwHAAAvCUlEQVR42u19eXxc1XX/99z73oxmJFmWF5nNGNvBGBvKYiCsFUlKAg1QloqGJm3S5JfQ/n7QJL9QSJomstKSlqyUpk2g4ZeShQQrJPmFJRBIbZGFzWa3Y7Cx8W7kRbYlSzPz3r2nf9z33rwZbaNlZt7I73w+z2NJI83Mu9+zfM8591wgllhiiSWWWGKJJZZYYokllliOEKHaertMYKB9OWjdUlD32lp7/1NVVqFl3cW8ZAm4owMMEMcKMCl4Z2rrhOheC2pZB+7sJBWDLfrS3s5iFSBaloI714LRQTpWgJLvHotWQFwM6I6iG9fezuJlG3McB0dD4XilVJqkPBFaASIGXkVFA8KSUApbpYUeDacbrr2j3sKuzg7KFRuy1uWQQ61prABeaNO2AmLJWnD4Bl3dzi054CxmdQZpOo+BhQCOJRKN0jbPEQLgGI5VAw+zubQCtKuyzNgpBG0kwmoSerVyrTWP3EZbite6sw0aVP1QqboK4FmGrg5y/W9d8dmB+Rr2pQz8CRGdJS0xkyTAGmBlbjSzBjMr7wPE+K+2+QKIAEFCEklASICEUQw3o/qFoDUgfoRYPvjgP9Fa//da29mqtleokgJ4VuA6E9O3fZJT/dPwXmj9UTAusBKinhlQDqCV0gRoNu+VQCACxeQ3korADAYbnQADIBJSStsohZPRigSeA4nvOoT7f9lB+wGgbQXLanmEigOpbQVLH/jv/EzvnJTd8GFm/UFpiZPAgOswWCvfugtQDPYaVwtmQBODQcKSCQEhACerdpOgH7AQd/+ig17PYwO6klmkyoGrnUU7gI4O0pe3c5qV+hQDN9pJ2eI6gHIcDSImQCC28FNXGTwPIaQlrSTgZnU/gHuVFv/42Bdpl5/sqFRYVBGgtbavtLo63uECwB9/1r0eoA4rKU50cwC7rssEQUQijuaPKPbMYCgIYdl1AsrR3Vrz7f2WvLOrg9zWdrbC3LBGFSAf67/n1oETLCvxdWmLq5QCtOO6AGQc4sReAQxF0rKsJKBy+hknp/72l19KPIt2NsntMnqD8oGvnYX/xi/9jPsBadHXpRSzchlXASAiijP3sRRRBSiZsCzW2mXNyx/5onUbALS1sSxXEbQsCuC/4Utv4iQ1ul+XCetvTEbHUURCxpnLWIaDIzMrIohEyiInpx/WWnz0sS/SrnAYHWkF8LM87/zb3jnJxtTP7aQ8J9vvKACC4nAnljGERXadbSlXbdeOuvLR25MvlIMXTCog/Tf47luzp1m2/KkQcr6bzbkgYcWLGss49MAVtm0R9CHl6A89erv902UfY3vN3eRM1kuIyQb/JTdnT7ds63EiOd/NOjH4Y5mAeSZLOY7SmqYJW3S+55bMNWvuJmfZx1bbkfIAfthzyc19p1vJuscFyVmuk/Pi/VhimTA/1kIQkSBWjtv22JfqfjJZ4dCEFcAnvCbssR4HxGzXcZQgkjHVjWUStUCTECBJ7Dq67fHb7Z9OhhJMTAG8VOcln+ptkYnUs8KS89xsTpEgGSd6YimLJ5CCQOTorD7/l19NrJloinQCCsDU1gaBJZCHMrnfWonEWYbwUhzzx1JOR6ClZQut9R7OOct++bXU9vZ20HhbJ8ZNglvbITs7SR3I5O5IpBJnuZkY/LFUghcLoVxHWQlrNlny++3tZnsswFQxBWhbwbKrg9z3/F32+mQy8Te5fseFiMEfS8WUQLqZnJtIJ/7wd5ncbZ3XkWptXzWuhMvYtaadBZaDL721/1jI5CsApmmlQRRvSoylstEQQEraluU4TuvjtyeeHA8fGLPVblsH6iTS6uaBbyWScnouk1VEQnJMemOpsCNgVkJowcT87Us+xWcsacCACYVK308wJqvdtsJo2CV/l21LpOvea8BPEgWbgOIrvipzEZFQjqPsVOJEiNxnOjpIt60YG6bHEAIxoR3UCiQS/bnfS0vOU67LcVdnLNXOCwGCIeCwo05+/Kt1b6IdVGoLdcngbW2HRAfpRH/25kQ6cYJ2XRWDP5YoUGJmzZZtJyHElwHitnWlG3YqUckIBFz6md5ZrOrWg6iZtWnrjxcgloiIFlKSq/Q5T3zZXtPW1ik6O68blRCXRIJbl0N2gVztZD5ip+0Zuf5snPOPJWqRkBaWtEg5twCJ60rdc1KCBTcFhtZ2JBOHs2uFZc3XrsOIw59YosYFSICADJFe8tjtqTdL2Vw/KohNgYE4eTj7XqsuuUC5uRj8sUSSC0BrZdUlUkrhIwCwCqtGxemoT7gYF2sA0ND/mxlMEDq+2bFE0gcAQuU0APxVazvXmS2UI7dIjKwAngtpvYWPI5Ln6ZxDAMs4BR1fUbwIJJST05adPNY6nLkQANraRsb4iES2FRBdYLY5c7mVrEs5A5mY/MYS+WwQSRJwxLUAnuheMjLPHRHMXTBj6lhnrmIdcjSxxBJdEcrRgObLLr2Jk492UNYM4hprCMRM6CB9+f89NAvAOcp1AXC8xTGWiHNhCK1yWtrWXJXoPx0A2v50hRwzB2hdbtpLs5Q4204mm7VyFEA0peLGWPJOfSpdmrW0pWCmdwBA95I2GkcIdLEJqFifZRHYTPetZcMAEHFB7Vprb+46mY6SI8tQ+vPLzSEjFNYFppq+H0wgL2Q/CwBa1g1v7oZVgJZ1nf4vncsaxDU3lN+cKCC8N+26QNZhOMr8jADUJQiWDIOfjxj4+59UKaBvgL2TXsz9SNiMhGUWXLN/f2pn9YlBWjFAOGPZXWx33kDOcG3S1nA61NkJ3drOFvoGFmhzF4gjrwLm85EH/JzLGMiaxZ3RCCw6XmDB0eaaPZ0wu0mgIXVkRz9ZB9i1X6Onl7F5N2PTTo3NuzT2HNTQGqhLEpK2cZGaw/4j0vpNWjnQzMc2bUELgB1m3zBKU4Bgk/HhvlnMdLxWjvepOdrA98A/kGVkcxqzmwUuWCpw0R9YOP1tEnOa4wL2UPK2Ywvvy4E+xqubFZ582cWa1xS271GwJKE+RWAzvzPqikBau9qyk0nXGVgAYIfZN1xiCLRuXScBgO0mjoOFNCuHQUTRw3/+DQliZB1j8RcdJ3Dp25O49Bwbs5qo4Nk6VMeOe1m9+xJaV0HA9AbChadauPBUC30DjJUvuHj4KQcvvWEUIVUnvPvIRawiYlRASpCLBQB+3b12VekK0L1kNgEAW86xlp2Gox1NgIwa8BmA8A6lOtincfRMwif+NIk/PjeBpJ0nuuwtLBEgYycwNCMuUghfKRpShCvOt3HF+Ta6XnJxz8NZrN+q0JAiWJKgtE8OOVJKQGx6IBiYF07qjCELBGhN6ahafGaGFEA2x1BK4/o/SuBDlyYxvcEsgtIG9CIG/NjBQ3nvyGyIsBBA62kWzlsi8cCTOdzzcA6HM4z6lIBS8M45iV5oxDwyhodRgIt9J3KSly9jpqiBn3GoX2N2E+HT70/hglPsPPBFbOknUxkk5b1pwiZc/64kli2ycNv3BrBui8L0RgGlPfYZGW9AhrQzLwaGT4WKkd2ICh16yVW4Cl+XNYO1hiSNg70KZywUuOeWelxwig2lzdOkAOLQvjzie1OlgUVzJe66uR6Xn2fhwCEFQRpgDdYjr2Hl8aNHZK5irNa38lafPRfEADQsobH/oIv3nG3hG59sQEuzsT4yPluyYiKFCYvqEoT2D6Xx0SsS6DnkQpIGoL21qo2Se8Q7OzkIeQAT9uw7pHDZuTa+8JF6wCvUxOFOFbwB5fnBx65IgQB86/9n0DxNBsWzPC+IrmUStQJ+SzAOHFJ4z9k2vvCRhuApIrb6VeUHQpiQ6KNXpHDDlUnjCUTYa1czgpigB9BVc2Ih8DNDEqO3X2Hx8YTPfbA+sCdxyBMBJfC8gdLAx65MY8tuhceec9DcaMHVvv33uxCoCiiaqAeoeDefIS8+mSJoOK5Cna3xj/+rEakkBU1csUTHE/h9Q5/5iwYsOJpweMCFgMlMcAEZRqQ6fsdAgit3MRsyBdYgaBwecHHLn9fjhKNlkN+PJXqcADCFs+UfboQgDa0VwMojxn48oSuMfq4lDsD5DAIzBGkc7FN455kJXHZuXZDtiSW6SqA0sOQEC395aQoH+hSE8MvK0eQEIkrgz//XWAqlGOkk46+vqo9j/hpSAs3A9X+UwglzCJms8eJR3WAwsgJUzFsVxv1ghgDjUJ+Lqy5MYsExVhz61BAfYAYa0wIffm8aAwOusf6aQ4WyCvIBPUEPULldbAB7blKzRk5pNKYZ77sk7eWUY3DVjBcQBt/vfnsKC44R6M8ogEyBjMHQzJHhwaMogK6gGvgZAw0hGIf7XVx0mo1jZllBN2csNeIFPIOWtAmXn1+HTNaFII8Isy4yz+WGvo46BwgRX3ildK1BULjywnSeEsRSc6EQAFx6XgrT6zUcx+MCKCbEMQkOiC8zg8DIZl3MnU04dWGyIMUWS+2R4aNmWDh1oY3+ARfkp7h98HP1M0JVLoTxoO5BgsZAxsW5S5NIJQlKx/F/rYo/TK31jBRc182vsy4ukFWPBJTUCqFR3iK23/LAHgdgaJx9cl3ISsRSq14AAM5clES6DnCVAgnyZrKUd5dtiUmgaoZAXixY8KjhKIWmNLB4XiLIKMRSozzAW7vjj7Jx7CyBrKNAMAYuWHOubst0dVshgtDHyw6wguMozJ5OOGqmVUCmYqlN0RqwJGHuHIlczoWf7cOgjFB1Rv9FoBDmhz6GADs5hWNnS0hJ0HH4U/s8wCO884+yoVwFYpPly4e9qIVmuHKEPwCH36VnEZRSmJYWfmIolikiTQ3kAV+HLCvykUCVwiCrFKhyeUyDlwXjoELIYCitMfcoG3kNiGOg2iYC5mHuUQmQyFeDA9CXaZ9AqU6gulsiudAKsJcnNjuKYplKYgnj5bWvAD7sq2zjRlEAnW9cmlSrEJr0EEp/klcF5jj4n3pkmM1ED7M/QABagyUZKACgckTjfpNZtDgAe3oVzgYNlRmIZYrR4fw6++uui1vgK7/uVSXBhf/3WUB8COXUVQEOsj+IyOYYq/pWAQV9QIU3p7J0xDdIxUP+aBKHbYUH9FIRBARNbt3Dn4ta/Jkm+3VKZ6X5omdw1JDfD1Slgk/VpkKw9+E5ZPt9C8EVBj57sy8ljQymiVal/S2dI23r9Ec70gSBL8TI71dzfpx8xex/KOOnwWUNP0rFrYVqaMAQu8F8q88V9ACa89Zw70HGs+sVXtum8VYPQ0rghDkCp8wXOOskCVvms7I0DiUDDPCzDvDseoW1b2ps7dbQDBw9g7D4eIG3L5bBcN/xbgIKK+pLb2i8vElh405GJstobiSceJzAWYsE5s0Rk6bYpd8HLugENV4/bxBpstNBE22GGzpmn1T0ex9dB/uAKxUT+uDvzwD/8fMcHn3OxZ6DXOCNtQYsC5h/lMBfXGLjqgusMYMz/Nz7Vzq4779dbOvWcENbPP33MqeZcPm5Nm64wkbCyn9/LIomBPDUOoVvPejg91s0MjkOAO7bmun1hPNPkfj41QkcPZMqqASh9krWwdpTQEe5TK8ZUQ4wZLBTgWyAD6w3dmr8/T1ZrH1TY1qaML2ehlTXbXsYn/9OFms2KPzD+5NIWKUpgW/sDmcYy+81SpZOEhrTQ//ioX7grodyeO41hds+ksDc2aIkJTAzYA2I73rIwV0POSAC6pNAqm7wwT5KA794xsWa1zU6PpjA+UtlZZSguP8/AnXOqvdacoVJrw+o3fsZ/+fOLDbsMCPWpTTAKL60BupsYMY0wo+7XHzuO1mz8btUP8fArXdn8cgzLmZOIyTsoV9HacCSwOwmwsubFG68M4ueXg4GTo34Wh54v/WggzseyKEhBdTXmd9TavDrAEBzI+FQP+Pj/57F8xsUhEAVeq+qn+4WpQCmMtOswySpvLfbVcAXvpfF7v3G8jtqZB3UbH7nqGbCI8+4+P4TjtnxpEcJRwi4+2EHK19SaGkmuKO8DjPgKKC5gbB5t8YX78uNihHfcv9urcJdD+XQMp2CPScjiauMYhMBy+/NoaeP/Tb9shk6BpvMlPbXuvy40lH3AJUU7cXd//2CiydfUZjeYEBZqrgamFZPuOcXDvYe4mD6wXDg37FX47uPO2huILhu6a/jK8Fjq108tU6NqGxEBszf+JkDKWlMhXulgXQS2LRL4wdPuCV5mxo3+GNVgHJPhQAqeYy7H0s/+JRCwhr7YdDMgC2BfYcYT6xxA+8wlMcAgF88q9A3YI5yGs8nkgL4+e/cERWaCHjxDYXXtmukk6Nb/qH+RkOK8MQaFwPZck/eK3XtK9cPfcR4AJ+0HjzMeG2bQtIeO1j8JRMErHldBxZ4KKsMAM+/bk5VHE9Y4Y8VWbtFYyA7tLfxv1zzmoLj8Lj4pGbAtoAd+xibdqlAKY4UOaIUAAC2dmscOGwIJ4/z7yQswpZuDUd5B0UMEf70Zxjb97LJGI3zdSzP2+zcz0NGEL6ibdxp6hbj9ZuCgJzD2LiToxqplE2s0dxjWZI0oxwJVs4VyOTyBHAigMnmRo6XXQVk3YmNdCECXNe855GkPzs5BmIy/k4pRohR9mg3SA3zREcjTjVpTFGQxx+vKAbqUzRibJ+wTR5e8cQAk7SBhtTIz2uqn7iREsL8nSNNjhgF8Is8x7cIzGgkOHp8NRjywoUFRxEs4RHRop/7B8jNaxHIOeN/HUcBLdMJx8wQQy6WD/qTjhOD3sdYeUBdgrDoWPMKFCvASOy93Nmg8olmIF0HnLZQIJPlcVU+fXCct1SO6urPXSqhNI8rDBIEZLKMM94mYVteAYuG5gDnnCyRqhsf2RZk+pPmH0WYN0cE7RTlzwJFYzyuiBT2y6wDPkCuvnB8HSCCgIwDzG0RaD1NBoR3qOcBwLuXSbRMF+PiAoYEU/BeaZj3oxk4+XiBZSdK9A6MPY0pBHB4gHHF+RZsqwJ1gGjh/8jiAP75tucslrjmIhv7DjHsEnXBPwdrIMv45LUJNHgWd7g0qNam3eCmq2z0DozN29gWsK+X8f53WVh6giipT+cT19pIJQ35LlXZLGnSwuecLHHtRbZpEznCWKGIotKWU/xy/83X2Vi2SGLPQYYlRwaNb1W7DzA++scJvOvM0ZvHhMcP/uQCCx94l423eowSyFF+x5JAdw/jolMlbrw6Yfr2xcheSWtg0XECf//nCfQOMFxl/g6NoMy2B/7ZTQJf+FACSRtlj/+jiKUjLgvkW+x0knDnjUlcdraFfYcYA1nzM3/Din8xDFCyDnDr+xK46WrbDOwt4c6RpwSfvj6Bv706gcMZ4FA/B0oVvshrzd7fy7jmIgtf/WvTdUolgNI/q/fyc83vJRPm7/iba8KvY3L+wJ6DjFPnS/znp5Ild51ORRl9KkQ+c1tmO1AZIuwrATPQVE/48g1JXHCKxANPutiwQ2Mgx0FGRQrT+/POMyx88N02TlsoxnQyvb+dkhn4myttLFsk8L3HXbz4hsLBwxxsWRTCKOSp8wWuu9jCZeeMfd+B9JTtkmUWFh8vcc8jDn671sW+g2zO6/UAbluEeXMIl51j4y/fPb59B+X1AeV4vfEqQEV2hBXpWIWGA/hKAABXXWDhqgssrN+qsWFH4Y6wk44TOGaWQcd4e+b91Og5iyXOWSyxrZvx+naFLd1GCY6eSTjxWIFFxxVOxBvrjjA/7Jo7m7D8gwnsP2TjtW0aG3dqZHKGk7ztWIGTjxdByFMx8A+3zlVuvqvypvhohEP+Xt3FxwssPl4MmT71ATZusuV3dBIwt4Uwt2XoWz/Ro2D9niFms4fhvKVyyJStHx4d6YePVHFT/Mg9gUDlelJ8wOkh2j4ETR5IxAivQ97rTEY3pp+xYh6c1vTDskqft1zJREf49fREFOBIE1EK46yh1yEaedJFLKUoQCU4QDXMfiyVF64CB5j4VIjJfpejnWjMsRZMafRXOgs0ijeObCgSy9QLL2sxBKo0CQYB/Zl4PuhUk/6MRvhQyEr6mxryAAwhCFt3DwQkLpYaD3w8BG57a6DiR97WyGjE/MUwWYsDh9xYAaaY7D/g5g/EqCQJ1hMKgcqhAcOTH80M2zIeIJvTSCbiM1JrPvb3lnDjtn6zD5v9Y5EqRYL1REOgCmZkGLAtge79OWzzwqD4sJhaJ7+EgazCmzv6kbAFmCtUBCkRuxEwsWSmApP5v7QIvYddvLKh13yEWANqVrS3dhu39mPnnqynAPlGJ4pAjCtGDYB0+cbWFZyHwRQ8AoTfPN8T84ApQoCferEH/RkNImGOxihYeyrraMRoewAf3RS2GkC6zsJTL/XgwCEHQlB8XnDNxv8EzYwnnt7jWf+idQ+WvnpWrnoKQEMrBANIJiR2dmfw1Mv7C1xpLDUW/hCwadthvLqxF+k6mW/zHgIEVCUlKJEEl3E3POXBH74FUhLu/8WOOAyq4fCHANz/6A4c7nchpQh4Xh77HDosOKpTIcpNzv2sgF8GBkEz0JC28dQL+7F24yEQEVTsBWoK/EIQDvQ6eGjVbtSnbC+b55/OF76iHAKViwCjkKSwd3PYuynMBBICmZzGt+7fFHuAGhPF5mCPHzy4FVt3DSCZtAzZBZlkh0eE849lPB8gemNRyAt38laA/B0coUtroGlaEg+t2oWnX9wHKWIvUBOxPwOSCDu7B/CfnZvR1Jj0hnrl1zl4HJQQqbylq34dIOQSTT1AgEgUPH7pnvVQioPUWSzRJr9EwB33vo69B3JI2BKAAEGYRwqtdXjdo5kF0uUlJ2EiRCHP4FkJzcC0hgSefnk//v2+DZAy9gKRDn0Uw5KER3+9Cz98ZCtmNCW9BriQdw/zgCoT4NI8QNneF4W+DpEiory1gIBShBlNdfjqd9bjt2v2wJIEV8VKEDnwa4aUhK27DuPWr7yIdJ1tjsL2vLhZTz/hUZT4KCf+JzIevXz2nzzdzBNfc5kbFdw0kkEolLAt3HTbaux4qx9W7Amil/UhQs7RuLHjORzodZFMGgUoDmfNRcHaG/sX+n+FfUA02i0LCLB/wyQgBEhIaAjU1dnY25PDxz73DHoO5WJSHBnS658qw/jEF1dj9doeTGtMQmkKGTGzlnlvQKFyQHVTfCISwAdAnrUgknnwBx5AQmmBpsY6vLj+AD5w828CJYjDoeqGPYIIDMZNHc/igce2YWZzCkobwxVcniKYtaWQEkS8Ga7M6B/0b54HCBBkoAwkBEgIKE2Y0ZTCC+t68IFP/Rpv7R0w4VCsBFUhvFIQsjmFG5c/jc7HtqJlZtqAP+zF/XWECMJcCngAqq4EoxbCyn+acaFSkJcJIhKhK68MrgJmTK/Dy68dwBU3/ArPvLgHUpqmq7hnqDIhj1KG8G7e3os/vXElfvr4drTMTMNVGLReeWUIpz4BEHv7YspcCeMJb4gpsxcI1wEKiJLnNoUFkAUSEhASJC24WmBaYx327M/hzz6xCt+8bz0EEYQw3kDHxYKyEF2lTMgjJeHnv9qKK2/4FV74/QHMaE7B1WTWSpg1M+vmh0Ayn9BAYcav2lK1qRCDXieYVhvOADFAGhAagAXyGsmJGUo7qEsloJSL9jtfxK9X78YtHz0Vp588M1iwuIViEiy+ZjCb5kQpCW/u6MOd967Fjx5+E6k6G9Ma66A0gWQe/PCNlcgDH0RgPwNEhvxyQfg7yXjCZGyKryAZJq83xNwPASI2NxLa3CpmQJiPJZihwWDtQpDEzOYUVj3zFn73fDf+/IoFuOF9izHv2IZYCcZp6ZnzoBfeQJ+9PRl8/2cb8Z8rXsfenhyap9cBJKHZgJ9Clp+EBaKQ5w64QJ4HRGVhqjMacRAZ5oKiCEGAg4qBZRSAQpfw4kePS2kNNDXWQSmFe1a8jh89uAkf/9ASfPxDp0BrDhaxktmRWhpuxz4shanahrcqrt3Qg/sf3oSHVm7Dtl39aGpM5jM9QYhjgcj2Hv3LC328gibBO23EM3Yoo/Uv+GATUwCNyg3sN9hmgvmHBAgMFgyCRL6s54dBhZ9Qa4CI0TIrjR27+4L0qObKER2fesgaHm3X1+/g9c0H8ZvVu/H4b3Zg7YYD6Ot3UZ9OYPaMNBSjKM3pW30JEXiCfPqTQmFPkPUnoLLjsaIeAg0KhRhEZCqJYK+QUriRRqCoyk3mGzlXoWlaHS5rnWtYfoWw6GdGAOC3a3aj97ADKWjQ7Y+Cavi2gwgYyChs2nYI+w5ksfHNg9i8vQ87u/sxkFFIJCTSKRszmxPQTFBMXo1G5q2/pwBC2EHoMzgDFC5+UYTuRBXPBxg2FAoIMQDyQiEaKmcVmiZBZN4sEbIZjeOPmYb5cxs9nSrvjTY95wb8+w9k8ZmvPIufPLbZKxBFU8gzNgCDmYKzjC1LIpGQSCZtpNNJr4cfUBBeYVLkMztFMT+EBQjbM1YmA8SeonCoBZ6pckpeCnarMxlulOWhUAhNkCYiMnPjCjcTFV1CEDK5HM4+bTZSSVlglcsV60tBkER4ZNU2LP/XNXhzex9mNKXysTUhQj6AMdRp234xMp+WJ2idb00J6jEeoS1QgEFxvxVKeYpgcYj9UzsqeA8mPhmuGraJQ6FQsRJ4iBJDA4pAEMJC69lzSuVA47f6XvfjvgMZ/NM3XsQPH3wDiYRlcuKK86AahLmI8QPOpyUDhfDz9UQhq59XAiI7UAC/VuPn+4Pqr9/YiHyLexQ/fwRPiClSAvL/L/yoCNCySAlML6FSjObpKZy5pLlsZDSw+pLw5HO7ccu/PIs3tvZiRnMdwOQdoSryLR4UUeCHNqeHB5NhEPhD1fhiDxBKc+Z/7ln+IN+PyIK/RAWo1oEV7GWGyOMBnhIQe0qAEDFmkGAcHnBw1pImHDMnNek1gLDV7+t38aW7X8L/+/EGSCkwa2YaSnnWU4QtHkXP8g/VhUnhvRhDgx+B9ZeFFV5RRHghgjOg8veBCzhehen+xBSgeue15D1BUCbwrD/7Wwe0n8BmCDAcJXD+GTNBAFxtdidNhvi1BCkJv35uNz53x/N4dcMBzJyeAoigtFn0fMpvOCWIoOUPvijcn03+Jhbhd3KKgq5OhL6fr/aKYH8HBXs9qqP8k3dIXlVPLMpbDwrVyoil9132TqKW0KyRsC2cf3ozgMmz/j6RdlyNO76zFnf81zoIITB7Rr3pefdAEu5jIirsdSFQxCKAIs8UFL/CSjB4MwuFgB62+sFGpiCJEYr5uYofenLOCIsqMTbhENgAMJclHDMnhcUL6k3GdIIaYDZ3G6v//Np9+IevrcGzL+/DjOY6CCGhvNelAkuYL/yYOBgonH8TFdxT4XQ2KgpZQh6gOByC39OPoXP8USa8NaoAwxBjfy8pEQQEMjnG6SdNw7R6a9wnuvviepu7tWZ89Z5X8Y3v/R6OIsyeaaw+Q0D4DV/B7rXC1l/fIhJFTAF4MCkNA7+QC4QmORQothj0O+EsUq2AvwQFqEohoESfxkH7BJEpRl105jSPsPK4FkAzg0CwJOG1TQfx2a+txsqnd2NGcxp1UppKqAxXQYtJYSgMilDL75CAHMQBUBgCIQx6KsoQFXq3ggJv1QjvcHjRE1CAqOEfFBonl48vXcVoSEmcsbghZHXHF+sDwF0/XI+vfPtV9A0otMxqgNIEzWJQ+m/IFCAVzr8Z3AIQLc9Kxe0JIQteoAhF5zj4hIyKvo6UTLQZLnL4L/pcDFPCz2Q1Fp9QhwXH1XlzKcdm9eG1/r6x9RBu/dJzWPn0W5jelERTYx1cnU//Dcp/BylAPx9OpnGPCjNAFAVgUNgq0zDeoSiWL6gPAFzweSiP+wiGPLW1H2ACKk0EZHMKbz9lupkUMYb2h+C5BNz38zdw2zdfwt6enNnbygI6HOsH1c5Q73u4OBTOgxMNCiuilwilIRQERYqAwUpMEaxtTH0SPIwiMAde4NxTG0pek3AD29adffj8Hc/joZXb0diQQHNTCq7X9VgIdN/qh74eIvQB+Ru/I0wIh3QGNFSANATopwbwS1MAAheeaxkh58YaREDOUWiZIXHaSaWlP32rL4nw40c34/N3PI+9PTnMmpGCZgHF4QxPeKdTqPkrZPULcuNBvBxtSzk0JaFhU6bDP49ryFqOQwGIyQpaBKOwiJ7F99+TII1MRuHcpWnMbLKgmYdVgLDV7943gC/82wvofORNpNM2ZkxPmX2tJCHEYMsfWH0/3g/NKyoY+xeO+8MFIIoM7Mdwr2n8zDIy0GeQZmvsCrBqlUeCebNmBY4Ei2OP9vr011CynKtx3mkNJuGlvW3ExVY/1Lb8819txfI7n8fWnf2YMT0FgLyilmXYs9fhCH9zN1mBMiDY5G2Az6FCEFNhTp0jFzLwlAxhhse+6RJQRJsAoHvJ0B96ZA9AtD/K88iV1kglCWctqff2tNJgq+81sB3qc9Dxby/guz/diHSdjVkz0maUR6ixiwaN9LCGbvqCzBe8isd9R73784gSAgE9Y/YAXS17zK45hb0sciCwiM4NNBMiCIxMTmPe0QmcPD81aInDDWwrnzYNbOs3HfSsvoCrKRTrDxfnW6G9rbJgWK8P9sEFr3gMRXSIvgaz2B2OakrzAEvaGAA06S3kZnIgKzHahK2KuTVPBAGZjMLZSxqRsEVAbhn5OfW9hx3887dexX/9ZCOkIMxq9qaXCQkhREGsj+I0J1mDWn2H3eUURBgx+CMkQisHGnrj2DlAh1lOlTvYLRNN24msBayz2lv9qll9/5FZwxxgpnHOKfWDrL4lCc+9sh+3fvkFvLx+P2ZOT5hYX3tzboqtPuUnGwShDxU3uUkUdngiNN2Aao8gTv3gRyinzyVhbwKArosv1ugqmQMQo53Fug7KnfaBbZuFtBconak6F+YQGXZcjeYmC2cvNQqgGbAlIZvT+Pq9G/DNH26A1gqzZ6Xhut7GASEKJxpQPrePUJwfJrpBn3tR0xfHIU+UE5+apC2gsrsPysyusFEf5CaG+xutq8zPWOk1EFakzJsgYCCrcfKCOsyZaUNrhm0RVq89iKtuehZfu3cjkkkL6VQCriIvvLG9CWaW92iDpA344zyEDRL5r/Oj/cSQ7cIx+COMf2IWMgEm8cqWe+dn0M4CoXFcJWaBDGmQJJ6BVhFZbW+aJAFZh3HmSemg/eGb92/H1+59A7mcg9kzUnAd16RKRejwPRFuXS5MbwYbusOnmQREt7i4FQM/8j5A2CBWq31j3jVMW+iwCtDVtUoDgFT0XC7X2y9Ippl19SpioS5QzUDSJrz3wunYuDWDT//rJvzuhX1oqpdIpAmu65r43Y8GiYq6NgtTn+a53hg/ypPcgOj66c2Y6NZKAkiwkwEBT5qsZiePlCwaQdoF0KH/4Pqtv5F2wwXa7VPepNOKW32wNhadGVnHwVEzBK55RyO+/ZPdONibxbR6wHVdaK0KZsIHm1NE4dz6ka1+OOQJ36YY/DVg/JmETaycbsdNLlzXOafPm/0yNg4AAK2ty33f/xBJC5w/zaBqF4NhWYSeQy6+ft9byCnGtAYLrvKtfeHgJoQnFoemmAVjvAsOcBsK/MXKGF9RvhhQZKWgif97XeecvrY2lsOBfxQOAHRdDI0uQMP9mZvr+wJAVjWZcLiB0dWEhrQFrZU5iVxIo+isA73O714qbFoblOEJ7d8tbGWILX7tBf9MzAxi/jEAdHevolHCpdE5NUD8B+/bslrYDWdq97AGICsO+6ARTnsVPg1mBbAydQHWYOiio+Tzo0qKQ53C9uXizdwx+Gs7/HF77GnO/DV3LzwIZjKHTQyTURztT7a2BmD/NgmbuOoV4aLJBaG25MI5lRZE6LCGfLyfH983NPgpBn/Nwh9KWA1gYMWauxcebGtjORL4S1KAri6Y6Dqpf+Rme/YKmZAFPQlVwH8YtFRwoPYQ8T/lj+0JH9rgb/amuI9n6mR/iIR2DysG/QcAdKJz1N8pobWBuLV1pfXSvfMPAPxdYTeAiVXliI0XBhVzUsoT1WBysRD5vboFXZzFRDc0s5Jikjs1yK9Wwm4Q2s10vfqjuS+jnQU6r1OToABAV9fFGmDSTP/h5voGQFKEunMqf5EZu8dBa7J/AJsEY6g2BvP9cPsCe0Q3vqbQxRqA9RUAaFtXmjsv2ee3tbHs7CR16p+9+U2ZbP5rN9fjEqiCe4qLyHDwraGOQhhqzAdqoGc/lnFiQwmrQWq393ev/Gj+BTDt+yWR1ZK7OzuXLGeASerE53Wut0eQPeiUogoFeoWzNik/wQyDzhnO79LK9/HE4J+C0T/ALgTpTxpj3Ulj+M3SJfAC79v8SSs582tOZr9LVAUv4HkCL+875Mcq5gtxenOK2n6wayWaLTez93uvrlj4lz5Gy6IAABPaIJY1Q2QPbnlW2unTlduvCCQr2yzKI36JSB1LFEsZYaAhbADoUQnrlHUntHSjAyg1/BlTCORnhIBOrLmbHEH8Ya2VC0hm1szsH7JciYsKvx5EhkZ4bnxNmUuDtbDSglXm4+vunbPbEF8aU1g+9h1endep1taV1ss/mv+CdvqXy8Q0iwFVefWnEq9YpqTxZy/0yR5Y8eqKhT9obV1pjSX0mWhsQK2tK2VX1zvcU6578xcyMe1S1zngkrdzJpZYyhz3KylTUmtnY0amlr3/bTP7OpaDR6v6TqYCwKSawKe37ZrlWvpFInmMVhmPD8QSS/lMP6SliSS0O3De2hULn0MbS4zD+o8vBMrrjkY76MXOY/Zo9/B7WevDgmwBjsD4iFimLvhJKiFSUumB961dsfC5tgmAf1LSI62tK62urne4J1+74U+sROMDrHPE2gURiXjFYpnEsIcBoaxEk+Vkez69rnPB7T72JsokMXElYKuri9zF1752jWU3djI7xFpxrASxTJ7pN+B3c/v/ft2Khf/sY26if3lSANrVRe6yZavt9Q+c9BN2+ttIJLQQlgDrOByKZRLCHqGtxDTLzR2YVPBPmgfwZdmy1faaNWc5p7RtvBqy/j5A12mVrXC1OJYpFPYoIiGErCel+j6z7v75/zKZ4J90BQiHQ0uvXn827IYHhVU3R+UOxUoQy1gNvyuslMXMDqvM+9f9eEHnZIO/LApQQIyvWTtP2k3fEVb9O1SuRzMziISIRwjGMiwcWTMTKSsx3VLuwGtK9//V+s4Tn0LrSgsTJLxDSVly9lu23Kvb2lh2PdDS071k2/dn6T9MkExeBGGT1o47xAbcWGIBM7skbSntRqHVwH19mT3XvPGTpRtbW1daW8oA/rJ5gEDaWZiZjMQnX7vxXcJK/auw00tV9gAYOi6axeJDXwEQMtFMyh14izh7y9oVC74LAJhgnn80KW+asoM0QGhtXWn9/oG3/Yp1z7kq1/tFCHtA2tMkmJk1q2CPcbyt6ci4vLU2a6+1sBokiSRpd+A7udzhs9auWPDd9nYWAFM5wV9+DxCWthXS36O5+M/eWCQ48Y8Euk7IOiinF8zapfwA/limcqDD0ESQwm4EmKF1rougPrt2xQm/DXPICrGOin54amuD8Lv2Fl+37VxB+Di0vlLajWnt9oNVVjNBEweDOmOZKqAHQMKWwq6HcnoByF+SoH9be/9xDwH+hivokSa51bgChLhBECIBJ1+z7URh4QMM/AUJaz4JG+wOQOssA1DmPDwqOpIllqiCHUz5c6wYgmRCCJkCoKFVZg8gfixZ3/NK57w1vmFEO8jHQ4XzTlWUdhZYhyDOW3b5jnSmHhcyq6uZ1XuI5Hxh1YNZgVUOzA6glWaYoRBR+Aix+OSNQMwCJIQ5eyEBIgusstDa2QXCKgHxgMr1rlr/syX7hlr/akg00NPOonXVKhGO++a1bq5rbLHP0OA/BKszmXAmtDpWyLoUiUT+QOq4+bS6wPcHEkCDtQPt9jsMsYuEeBkQaxj6t26i/pmNP5h1KKCDbSw7l4CrYfGjqQAhjoA2iDYAxbt7ln2M7YGeTUcz2SeAaR6xWqCVk4YQi+LCWjWAQ0wkSWtnqxDJ/WDaqeFskUq+kc1kt298dFG2MAnC0qxrZWP8WrYuhLYVsrWVLbRxXC+oNWlnkV87pugqci0pRPtywrrl1Nq9ioCLAQAtLbH5r6Z0B2uxCi0tF7MJbUzxM747scQSSyyxxBJLLLHEEkssscQSIfkf6ULBDMN5/jsAAAAASUVORK5CYII=")
MANIFEST = json.dumps({
    "name": "LAN Chat", "short_name": "LAN Chat", "start_url": "/", "display": "standalone",
    "background_color": "#3b6ef5", "theme_color": "#3b6ef5",
    "icons": [{"src": "/icon.png", "sizes": "192x192", "type": "image/png"}],
}, ensure_ascii=False)

TOAST_HTML = r"""<!doctype html><html><head><meta charset="utf-8"><style>
:root{--bg:#ffffff;--text:#1d1f23;--muted:#737a85;--line:#dfe2e7}
@media (prefers-color-scheme: dark){:root{--bg:#23262d;--text:#eceef2;--muted:#9aa1ab;--line:#353942}}
html,body{margin:0;height:100%;overflow:hidden;background:var(--bg);color:var(--text);
  font-family:"Segoe UI","Malgun Gothic",sans-serif;-webkit-user-select:none;user-select:none;cursor:pointer}
body{box-sizing:border-box;border:1px solid var(--line);display:flex;gap:12px;align-items:center;padding:12px 14px}
.av{flex:none;width:44px;height:44px;border-radius:50%;background:hsl(__HUE__ 55% 52%);color:#fff;font-weight:700;
  font-size:19px;display:flex;align-items:center;justify-content:center}
.c{flex:1;min-width:0}
.n{font-weight:700;font-size:14px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;padding-right:18px}
.b{font-size:13px;color:var(--muted);margin-top:2px;line-height:1.35;display:-webkit-box;-webkit-line-clamp:2;
  -webkit-box-orient:vertical;overflow:hidden;word-break:break-word}
.x{position:absolute;top:6px;right:8px;border:none;background:transparent;color:var(--muted);font-size:16px;cursor:pointer;padding:2px 4px}
.x:hover{color:var(--text)}
.bar{position:absolute;left:0;bottom:0;height:3px;background:#3b6ef5;width:100%;transform-origin:left;animation:t 6s linear forwards}
body:hover .bar{animation-play-state:paused}
@keyframes t{to{transform:scaleX(0)}}
</style></head><body>
<div class="av">__INITIAL__</div>
<div class="c"><div class="n">__NAME__</div><div class="b">__BODY__</div></div>
<button class="x" id="x" title="Close">✕</button><div class="bar" id="bar"></div>
<script>
const PEER = __PEER__;
const api = () => window.pywebview && window.pywebview.api;
document.getElementById('x').addEventListener('click', e => { e.stopPropagation(); api() && api().toast_close(); });
document.body.addEventListener('click', () => api() && api().toast_open(PEER));
document.getElementById('bar').addEventListener('animationend', () => api() && api().toast_close());
</script></body></html>"""

# ====================================================================== page
PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#3b6ef5">
<title>LAN Chat</title>
<link rel="icon" href="/icon.png">
<link rel="apple-touch-icon" href="/icon.png">
<link rel="manifest" href="/manifest.webmanifest">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="LAN Chat">
<style>
:root{
  --bg:#f3f4f6; --panel:#ffffff; --text:#1d1f23; --muted:#737a85; --line:#e2e4e8; --hover:#f0f2f5;
  --bubble:#ffffff; --me:#3b6ef5; --accent:#3b6ef5; --on:#22a55b; --away:#e0a100; --busy:#d9443a; --off:#a3a8b0;
  --chatbg:#dfe7f1; --daybg:rgba(0,0,0,.08);
}
@media (prefers-color-scheme: dark){
  :root{ --bg:#15171b; --panel:#1d2026; --text:#e8eaee; --muted:#8c929c; --line:#2d313a; --hover:#262a31;
         --bubble:#2c3038; --accent:#6d93ff; --off:#5d626b; --chatbg:#16181d; --daybg:rgba(255,255,255,.07); }
}
*{box-sizing:border-box}
html,body{margin:0;height:100%;background:var(--bg);color:var(--text);
  font-family:-apple-system,BlinkMacSystemFont,"Segoe UI","Malgun Gothic","Apple SD Gothic Neo",sans-serif;font-size:14px}
body{display:flex;height:100vh;height:100dvh;overflow:hidden}
button,input,select,textarea{font:inherit;color:inherit}
.hidden{display:none!important}
.col{display:flex;flex-direction:column;min-height:0}

/* ---------- panes */
#listPane{display:flex;flex-direction:column;width:100%;background:var(--panel);min-width:0}
#chatPane{display:flex;flex-direction:column;flex:1;min-width:0}
body.v-list #chatPane{display:none}
body.v-chat #listPane{display:none}
body.v-mobile #chatPane{display:none}
body.v-mobile.in-chat #listPane{display:none}
body.v-mobile.in-chat #chatPane{display:flex}
@media (min-width:760px){
  body.v-mobile #listPane{display:flex!important;width:300px;flex:none;border-right:1px solid var(--line)}
  body.v-mobile #chatPane{display:flex!important}
  body.v-mobile .back{display:none}
}
.pad-top{padding-top:env(safe-area-inset-top)}

/* ---------- register */
#reg{margin:auto;width:min(340px,calc(100% - 32px));background:var(--panel);border:1px solid var(--line);
  border-radius:16px;padding:24px}
#reg h2{margin:0 0 6px;font-size:20px}
#reg p{margin:0 0 16px;color:var(--muted);line-height:1.5}
.field{width:100%;border:1px solid var(--line);background:var(--bg);border-radius:10px;padding:11px 12px;font-size:16px;outline:none}
.field:focus{border-color:var(--accent)}
.primary{width:100%;margin-top:12px;border:none;background:var(--accent);color:#fff;border-radius:10px;padding:12px;font-size:15px;cursor:pointer}

/* ---------- me box */
.mebox{display:flex;gap:12px;align-items:center;padding:14px 14px 10px;border-bottom:1px solid var(--line)}
.mefields{flex:1;min-width:0;display:flex;flex-direction:column;gap:2px}
.plain{border:1px solid transparent;background:transparent;border-radius:6px;padding:2px 6px;margin-left:-6px;outline:none;width:100%}
.plain:hover{border-color:var(--line)}
.plain:focus{border-color:var(--accent);background:var(--bg)}
.plain.name{font-weight:700;font-size:16px}
.plain.note{color:var(--muted);font-size:13px}
.merow{display:flex;align-items:center;gap:6px}
.merow select{border:none;background:transparent;color:var(--muted);font-size:13px;padding:0;cursor:pointer;outline:none}
.merow select option{color:#000}
.tools{display:flex;gap:6px;padding:8px 12px;border-bottom:1px solid var(--line);flex-wrap:wrap}
.langsel{margin-left:auto;background:transparent;color:var(--muted);outline:none}
.langsel option{color:#000}
.tbtn{border:1px solid var(--line);background:transparent;border-radius:8px;padding:6px 10px;cursor:pointer;font-size:13px}
.tbtn:hover{background:var(--hover)}

/* ---------- avatar */
.av{position:relative;flex:none;width:36px;height:36px;border-radius:50%;display:flex;align-items:center;justify-content:center;
  color:#fff;font-weight:700;font-size:15px}
.av.big{width:46px;height:46px;font-size:19px}
.sd{width:10px;height:10px;border-radius:50%;background:var(--off);display:inline-block;flex:none}
.av .sd{position:absolute;right:-1px;bottom:-1px;border:2px solid var(--panel);width:13px;height:13px}
.st-online{background:var(--on)} .st-away{background:var(--away)} .st-busy{background:var(--busy)} .st-offline{background:var(--off)}

/* ---------- contacts */
.contacts{flex:1;overflow-y:auto;padding:4px 0 12px}
.sec{font-size:12px;font-weight:700;color:var(--muted);padding:12px 14px 4px}
.contact{display:flex;align-items:center;gap:10px;padding:8px 14px;cursor:pointer;user-select:none}
.contact:hover,.contact.sel{background:var(--hover)}
.contact.off{opacity:.55}
.ci{flex:1;min-width:0}
.cn{font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.cnote{font-size:12px;color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.kind{font-size:11px;margin-left:4px;opacity:.7}
.badge{flex:none;min-width:20px;height:20px;border-radius:10px;background:var(--busy);color:#fff;font-size:12px;font-weight:700;
  display:flex;align-items:center;justify-content:center;padding:0 6px}
.nobody{color:var(--muted);text-align:center;padding:30px 20px;line-height:1.6;font-size:13px}

/* ---------- chat */
.chead{position:relative;display:flex;align-items:center;gap:10px;padding:10px 14px;background:var(--panel);border-bottom:1px solid var(--line)}
.hbtn{flex:none;border:none;background:transparent;color:var(--muted);font-size:20px;line-height:1;width:34px;height:34px;border-radius:8px;cursor:pointer}
.hbtn:hover{background:var(--hover);color:var(--text)}
.menu{position:absolute;right:12px;top:52px;z-index:30;min-width:190px;background:var(--panel);border:1px solid var(--line);
  border-radius:10px;box-shadow:0 8px 24px rgba(0,0,0,.18);padding:6px}
.menu button{display:block;width:100%;text-align:left;border:none;background:transparent;padding:9px 12px;border-radius:7px;cursor:pointer;font-size:14px}
.menu button:hover{background:var(--hover)}
.menu .danger{color:var(--busy)}
.drawer{position:fixed;inset:0;z-index:35;background:rgba(0,0,0,.35);display:flex;justify-content:flex-end}
.dpanel{width:min(420px,100%);height:100%;background:var(--panel);display:flex;flex-direction:column;box-shadow:-8px 0 24px rgba(0,0,0,.2)}
.dhead{display:flex;align-items:center;gap:8px;padding:12px 14px;border-bottom:1px solid var(--line);padding-top:max(12px,env(safe-area-inset-top))}
.dhead .back{display:block!important}
.dtitle{font-weight:700;font-size:16px}
.dbody{flex:1;overflow-y:auto;padding:12px 14px calc(16px + env(safe-area-inset-bottom))}
.dsec{font-size:12.5px;font-weight:700;color:var(--muted);margin:6px 0 8px}
.grid3{display:grid;grid-template-columns:repeat(3,1fr);gap:4px;margin-bottom:18px}
.grid3 a{display:block;aspect-ratio:1;border-radius:8px;overflow:hidden;background:var(--hover)}
.grid3 img{width:100%;height:100%;object-fit:cover;display:block}
.frow{display:flex;align-items:center;gap:10px;padding:10px 0;border-bottom:1px solid var(--line)}
.frow .fi{flex:1;min-width:0}
.frow .fn{font-size:14px}
.frow .fm{font-size:12px;color:var(--muted);margin-top:2px}
.frow .facts{margin-top:6px}
.locbody{font-size:14px;line-height:1.6;margin:8px 0 6px}
.locbody .path{display:block;margin:8px 0;padding:10px 12px;border-radius:10px;background:var(--hover);font-weight:700;word-break:break-all}
.locbody ol{padding-left:20px;margin:6px 0}
.locbody .hint{color:var(--muted);font-size:12.5px}
.tipbox{border:1px solid var(--accent);border-radius:10px;padding:10px 12px;margin:8px 0 12px;background:color-mix(in srgb,var(--accent) 8%,transparent)}
.dempty{color:var(--muted);text-align:center;padding:40px 0}
.mcard .row{display:flex;gap:8px;margin-top:6px}
.mcard .row button{flex:1;margin-top:0}
.primary.secondary{background:transparent;color:var(--text);border:1px solid var(--line)}
.primary.danger{background:var(--busy)}

/* scrollbars */
:root{--sb:rgba(0,0,0,.22);--sbh:rgba(0,0,0,.38)}
@media (prefers-color-scheme: dark){:root{--sb:rgba(255,255,255,.18);--sbh:rgba(255,255,255,.32)}}
::-webkit-scrollbar{width:10px;height:10px}
::-webkit-scrollbar-track{background:transparent}
::-webkit-scrollbar-thumb{background:var(--sb);border-radius:10px;border:3px solid transparent;background-clip:padding-box;min-height:40px}
::-webkit-scrollbar-thumb:hover{background:var(--sbh);border:3px solid transparent;background-clip:padding-box}
::-webkit-scrollbar-button,::-webkit-scrollbar-corner{display:none;width:0;height:0}
@supports not selector(::-webkit-scrollbar){*{scrollbar-width:thin;scrollbar-color:var(--sb) transparent}}
.back{border:none;background:transparent;font-size:28px;line-height:1;padding:0 6px 4px 0;cursor:pointer}
.pinfo{flex:1;min-width:0}
.pname{font-weight:700;font-size:15px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.pstat{font-size:12px;color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.notice{font-size:12px;color:var(--muted);background:var(--panel);border-bottom:1px solid var(--line);padding:6px 14px}
.msgs{flex:1;overflow-y:auto;padding:10px 12px 14px;display:flex;flex-direction:column;background:var(--chatbg)}
.msgs,.msgs *{-webkit-user-select:text;user-select:text}
.bubble ::selection{background:#ffe38a;color:#000}

/* 메시지 한 줄: [프로필] [이름 / 말풍선 + 시간] */
.msg{display:flex;align-items:flex-start;gap:8px;margin-top:3px;max-width:100%}
.msg.first{margin-top:12px}
.msg .pav{flex:none;width:38px;height:38px;border-radius:14px;display:flex;align-items:center;justify-content:center;
  color:#fff;font-weight:700;font-size:15px;visibility:hidden}
.msg.first .pav{visibility:visible}
.msg.me .pav{display:none}
.mcol{display:flex;flex-direction:column;align-items:flex-start;min-width:0;max-width:calc(100% - 46px)}
.msg.me{justify-content:flex-end}
.msg.me .mcol{align-items:flex-end;max-width:100%}
.pname2{font-size:12.5px;color:var(--text);opacity:.85;margin:0 0 4px 2px;display:none}
.msg.first:not(.me) .pname2{display:block}
.line{display:flex;align-items:flex-end;gap:5px;max-width:100%}
.msg.me .line{flex-direction:row-reverse}
.side{flex:none;display:flex;flex-direction:column;align-items:flex-start;font-size:10.5px;color:var(--muted);line-height:1.3;padding-bottom:1px;white-space:nowrap}
.msg.me .side{align-items:flex-end}
.side .tm{visibility:hidden}
.msg.last .side .tm{visibility:visible}
.side .st{color:var(--muted)}
.side .bad{color:var(--busy)}

.bubble{position:relative;background:var(--bubble);color:var(--text);border-radius:4px 16px 16px 16px;padding:8px 11px;
  white-space:pre-wrap;word-break:break-word;line-height:1.45;font-size:14.5px;max-width:min(520px, 72vw);min-width:0;
  box-shadow:0 1px 1px rgba(0,0,0,.06)}
.msg:not(.first) .bubble{border-radius:16px}
.msg.me .bubble{background:var(--me);color:#fff;border-radius:16px 4px 16px 16px}
.msg.me:not(.first) .bubble{border-radius:16px}
.msg.first:not(.me) .bubble::before{content:"";position:absolute;left:-6px;top:0;border-top:9px solid var(--bubble);border-left:8px solid transparent}
.msg.first.me .bubble::before{content:"";position:absolute;right:-6px;top:0;border-top:9px solid var(--me);border-right:8px solid transparent}
.bubble a{color:inherit}
.imgb{padding:0;overflow:hidden;background:transparent!important;box-shadow:none}
.imgb::before{display:none}
.imgb img{display:block;max-width:100%;max-height:300px;border-radius:12px;cursor:pointer}
.filebox{display:flex;align-items:center;gap:10px;white-space:normal;min-width:200px}
.fic{width:40px;height:40px;border-radius:10px;background:rgba(127,127,127,.18);display:flex;align-items:center;justify-content:center;font-size:19px;flex:none}
.fn{font-weight:600;word-break:break-all}
.fs{font-size:12px;opacity:.75}
.facts{display:flex;gap:6px;margin-top:5px;flex-wrap:wrap}
.facts button,.facts a{border:1px solid currentColor;background:transparent;border-radius:6px;padding:2px 8px;font-size:12px;
  cursor:pointer;text-decoration:none;color:inherit;opacity:.85}
.fline{font-size:11.5px;color:var(--muted);margin:4px 2px 0;display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.fline .facts{margin:0}
.day{align-self:center;margin:16px 0 4px;font-size:11.5px;color:var(--muted);background:var(--daybg);border-radius:999px;padding:4px 14px}
.prog{align-self:flex-end;font-size:12px;color:var(--muted);width:60%}
.bar{height:5px;background:var(--line);border-radius:3px;overflow:hidden;margin-top:4px}
.bar i{display:block;height:100%;width:0;background:var(--accent)}
.empty{margin:auto;color:var(--muted);text-align:center;padding:20px;line-height:1.6}
.composer{display:flex;gap:8px;align-items:flex-end;padding:10px 12px;background:var(--panel);border-top:1px solid var(--line);
  padding-bottom:max(10px,env(safe-area-inset-bottom))}
.composer textarea{flex:1;resize:none;overflow-y:hidden;border:1px solid var(--line);background:var(--bg);border-radius:12px;padding:9px 12px;
  font-size:16px;max-height:140px;min-height:40px;outline:none}
.composer textarea:focus{border-color:var(--accent)}
.btn{flex:none;height:40px;min-width:40px;border:none;border-radius:12px;cursor:pointer;font-size:14px;padding:0 14px;background:var(--accent);color:#fff}
.btn.ghost{background:transparent;color:var(--muted);border:1px solid var(--line);padding:0;width:40px;display:flex;align-items:center;justify-content:center}
.btn.ghost:hover{color:var(--text);background:var(--hover)}

/* ---------- misc */
.drop{position:fixed;inset:0;background:rgba(59,110,245,.15);border:3px dashed var(--accent);display:none;align-items:center;
  justify-content:center;font-size:18px;color:var(--accent);pointer-events:none;z-index:20}
.drop.show{display:flex}
#connBar{position:fixed;left:50%;top:10px;transform:translateX(-50%);background:var(--busy);color:#fff;font-size:13px;
  padding:6px 14px;border-radius:999px;z-index:30}
.modal{position:fixed;inset:0;background:rgba(0,0,0,.45);display:flex;align-items:center;justify-content:center;z-index:40}
.mcard{background:var(--panel);border-radius:14px;padding:18px;width:min(320px,calc(100% - 24px));max-height:90vh;overflow:auto;text-align:center}
.mcard h3{margin:0 0 6px;font-size:16px}
.mcard p{margin:0 0 12px;color:var(--muted);font-size:13px;line-height:1.5}
.mcard img{width:200px;height:200px;border-radius:8px;background:#fff}
.mcard code{display:block;margin:6px 0 14px;font-size:14px;user-select:all;word-break:break-all}
</style>
</head>
<body>
<div id="connBar" class="hidden" data-i18n="reconnecting"></div>

<form id="reg" class="hidden">
  <h2>LAN Chat</h2>
  <p data-i18n-html="regHelp"></p>
  <input id="regName" class="field" maxlength="30" data-i18n-ph="regPh" autocomplete="off">
  <button class="primary" type="submit" data-i18n="start"></button>
</form>

<section id="listPane" class="hidden pad-top">
  <div class="mebox">
    <div class="av big" id="meAv"></div>
    <div class="mefields">
      <input id="meName" class="plain name" maxlength="30" spellcheck="false" data-i18n-title="rename">
      <div class="merow"><span class="sd" id="meDot"></span>
        <select id="meStatus"><option value="online" data-i18n="online"></option><option value="away" data-i18n="away"></option><option value="busy" data-i18n="busyMute"></option></select></div>
      <input id="meNote" class="plain note" maxlength="60" data-i18n-ph="notePh" spellcheck="false">
    </div>
  </div>
  <div class="tools" id="deskTools"><button class="tbtn hidden" id="phoneBtn" type="button" data-i18n="phoneBtn"></button><button class="tbtn hidden" id="folderBtn" type="button" data-i18n="folderBtn"></button><button class="tbtn hidden" id="saveLocBtn" type="button" data-i18n="saveLocBtn"></button>
    <select class="tbtn langsel" id="langSel" title="Language"><option value="en">English</option><option value="ko">한국어</option></select></div>
  <div id="contacts" class="contacts"></div>
</section>

<section id="chatPane" class="hidden">
  <div id="chatEmpty" class="empty" data-i18n="pick"></div>
  <div id="chatMain" class="col hidden" style="flex:1">
    <header class="chead pad-top">
      <button class="back" id="backBtn" type="button">‹</button>
      <div class="av" id="peerAv"></div>
      <div class="pinfo"><div class="pname" id="peerName"></div><div class="pstat" id="peerStat"></div></div>
      <button class="hbtn" id="menuBtn" type="button" title="More">⋯</button>
      <div class="menu hidden" id="chatMenu"><button type="button" id="filesBtn" data-i18n="filesMenu"></button><button type="button" class="danger" id="clearBtn" data-i18n="clearChat"></button></div>
    </header>
    <div class="notice hidden" id="offNotice" data-i18n="offNotice"></div>
    <div id="msgs" class="msgs"></div>
    <form id="form" class="composer">
      <button class="btn ghost" type="button" id="attach" data-i18n-title="sendFile"><svg viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M21.44 11.05l-9.19 9.19a6 6 0 0 1-8.49-8.49l9.19-9.19a4 4 0 0 1 5.66 5.66l-9.2 9.19a2 2 0 0 1-2.83-2.83l8.49-8.48"/></svg></button>
      <input type="file" id="file" multiple hidden>
      <textarea id="input" rows="1" data-i18n-ph="msgPh" enterkeyhint="send"></textarea>
      <button class="btn" type="submit" data-i18n="send"></button>
    </form>
  </div>
</section>

<div class="modal hidden" id="locModal">
  <div class="mcard" style="text-align:left">
    <h3 data-i18n="locTitle" style="text-align:center"></h3>
    <div id="locBody" class="locbody"></div>
    <button class="primary secondary" type="button" id="locClose" data-i18n="close"></button>
  </div>
</div>
<div class="modal hidden" id="confirmModal">
  <div class="mcard">
    <h3 id="confirmTitle"></h3>
    <p id="confirmBody"></p>
    <div class="row"><button class="primary secondary" type="button" id="confirmNo" data-i18n="cancel"></button>
      <button class="primary danger" type="button" id="confirmYes" data-i18n="del"></button></div>
  </div>
</div>
<div class="modal hidden" id="phoneModal">
  <div class="mcard">
    <h3 data-i18n="phoneTitle"></h3>
    <p data-i18n-html="phoneHelp"></p>
    <div id="phoneList"></div>
    <button class="primary" type="button" id="phoneClose" data-i18n="close"></button>
  </div>
</div>
<div class="drawer hidden" id="drawer">
  <div class="dpanel">
    <header class="dhead"><button class="back" id="drawerBack" type="button">‹</button><div class="dtitle" data-i18n="filesTitle" style="flex:1"></div><button class="tbtn" id="drawerLocBtn" type="button" data-i18n="folderBtn"></button></header>
    <div class="dbody" id="drawerBody"></div>
  </div>
</div>
<div class="drop" id="drop" data-i18n="drop"></div>

<script>
const MAX_UPLOAD = __MAX_UPLOAD__;
const $ = s => document.querySelector(s);
const qs = new URLSearchParams(location.search);
const DESK_T = qs.get('t') || '';
const IS_DESK = !!DESK_T;
const VIEW = IS_DESK ? (qs.get('view') === 'chat' ? 'chat' : 'list') : 'mobile';
const SYS_LANG = 'en';   // 기본 언어: 영어 (한국어는 언어 선택에서)
let LANG = SYS_LANG;
const I18N = {
  ko: {
    saveLocBtn:'📂 저장 위치', locTitle:'📂 파일 저장 위치',
    locAndroid:'<span class="path">내 파일 → 다운로드 (Download)</span>저장한 파일은 폰의 <b>다운로드</b> 폴더에 들어갑니다.<ol><li><b>내 파일</b>(삼성) 또는 <b>Files</b>(구글) 앱을 엽니다</li><li><b>다운로드</b>를 누릅니다</li></ol><span class="hint">브라우저 설정에서 저장 위치를 바꿨다면 그 폴더에 있습니다. 저장 직후 뜨는 다운로드 알림을 눌러도 바로 열립니다.</span>',
    locIOS:'<span class="path">파일 앱 → iCloud Drive → 다운로드</span>저장한 파일은 <b>파일</b> 앱의 <b>다운로드</b> 폴더에 들어갑니다.<ol><li><b>파일</b> 앱을 엽니다</li><li><b>둘러보기 → iCloud Drive(또는 나의 iPhone) → 다운로드</b></li></ol><span class="hint">사진은 파일 대신 사진을 길게 눌러 <b>사진 앱에 저장</b>할 수도 있습니다. 저장 위치는 설정 → Safari → 다운로드에서 바꿀 수 있습니다.</span>',
    locDesktop:'<span class="path">브라우저의 다운로드 폴더</span>보통 <b>다운로드</b> 폴더에 저장됩니다. 브라우저에서 <b>Ctrl+J</b>(Mac은 ⌥⌘L)를 누르면 다운로드 목록과 폴더를 바로 열 수 있습니다.',
    tipTitle:'<b>가장 빠른 방법: 브라우저의 다운로드 목록</b><br>', tipChrome:'Chrome 오른쪽 위 <b>⋮ → 다운로드</b>를 누르면 받은 파일 목록이 나오고, 누르면 바로 열립니다.',
    tipSamsung:'삼성 인터넷 아래쪽 <b>☰ → 다운로드 기록</b>을 누르면 받은 파일 목록이 나오고, 누르면 바로 열립니다.',
    tipFirefox:'Firefox <b>⋮ → 다운로드</b>를 누르면 받은 파일 목록이 나옵니다.',
    tipSafari:'주소창 왼쪽의 <b>가가(aA) 버튼 → 다운로드</b>를 누르면 받은 파일 목록이 나오고, 누르면 바로 열립니다.',
    filesMenu:'📁 사진·파일', filesTitle:'사진·파일', photos:'사진', filesSec:'파일', noFiles:'아직 주고받은 파일이 없습니다', fromMe:'보냄', fromThem:'받음',
    clearChat:'🗑 대화 내용 삭제', clearTitle:'대화 내용을 삭제할까요?', clearBody:'{name}님과의 모든 메시지가 이 기기에서 삭제됩니다. 상대방의 대화 내용은 그대로 남고, 받은 파일 폴더에 저장된 파일도 지워지지 않습니다.', cancel:'취소', del:'삭제', noMsgs:'메시지가 없습니다',
    reconnecting:'연결이 끊어졌습니다. 다시 연결하는 중…', regHelp:'이 기기에서 사용할 이름을 입력하세요.<br>다른 사람의 목록에 이 이름으로 표시됩니다.',
    regPh:'예: 내 폰', start:'시작하기', rename:'이름 바꾸기', online:'온라인', away:'자리 비움', busy:'다른 용무 중',
    busyMute:'다른 용무 중 (알림음 끔)', offline:'오프라인', notePh:'상태 메시지 입력', phoneBtn:'📱 폰 연결', folderBtn:'📂 받은 파일',
    pick:'대화할 상대를 선택하세요', offNotice:'상대가 오프라인입니다. 보낸 메시지는 상대가 접속하면 전달됩니다.',
    sendFile:'파일 보내기', msgPh:'메시지 입력', send:'전송', phoneTitle:'폰에서 접속하기',
    phoneHelp:'폰을 이 PC와 같은 Wi-Fi에 연결한 뒤<br>카메라로 QR을 찍거나 주소를 입력하세요.', close:'닫기', drop:'여기에 놓으면 전송됩니다',
    cantConnect:'연결할 수 없습니다.<br>LAN Chat이 실행 중인지 확인하세요.', regFail:'등록 실패: ',
    nobody:'아직 아무도 없습니다.<br>다른 PC에서 LAN Chat을 실행하거나<br>', nobodyDesk:'📱 폰 연결로 폰을 추가하세요.', nobodyWeb:'다른 기기에서 접속해 보세요.',
    chat:'대화', open:'열기', showFolder:'폴더에서 보기', save:'저장', pending:'대기 중', failed:'전송 실패', sendFail:'전송 실패: ',
    tooBig:'파일이 너무 큽니다', sending:'보내는 중…', fileFail:'파일 전송 실패', connErr:'연결 오류',
    otherAddr:'다른 네트워크 주소', noAddr:'네트워크 주소를 찾지 못했습니다. Wi-Fi/LAN 연결을 확인하세요.'
  },
  en: {
    saveLocBtn:'📂 Save location', locTitle:'📂 Where files are saved',
    locAndroid:'<span class="path">Files → Downloads</span>Files you save go to your phone\'s <b>Download</b> folder.<ol><li>Open <b>My Files</b> (Samsung) or <b>Files</b> (Google)</li><li>Tap <b>Downloads</b></li></ol><span class="hint">If you changed the download location in your browser settings, look there. You can also tap the download notification right after saving.</span>',
    locIOS:'<span class="path">Files → iCloud Drive → Downloads</span>Files you save go to the <b>Downloads</b> folder in the <b>Files</b> app.<ol><li>Open the <b>Files</b> app</li><li><b>Browse → iCloud Drive (or On My iPhone) → Downloads</b></li></ol><span class="hint">For photos, you can also long-press the photo and choose <b>Save to Photos</b>. The location can be changed in Settings → Safari → Downloads.</span>',
    locDesktop:'<span class="path">Your browser\'s Downloads folder</span>Files are usually saved to <b>Downloads</b>. Press <b>Ctrl+J</b> (⌥⌘L on Mac) in your browser to open the download list and folder.',
    tipTitle:'<b>Fastest way: your browser\'s download list</b><br>', tipChrome:'In Chrome, tap <b>⋮ → Downloads</b> to see the files you saved. Tap one to open it.',
    tipSamsung:'In Samsung Internet, tap <b>☰ → Download history</b> to see the files you saved. Tap one to open it.',
    tipFirefox:'In Firefox, tap <b>⋮ → Downloads</b> to see the files you saved.',
    tipSafari:'Tap the <b>aA button → Downloads</b> in the address bar to see the files you saved. Tap one to open it.',
    filesMenu:'📁 Photos & files', filesTitle:'Photos & files', photos:'Photos', filesSec:'Files', noFiles:'No files shared yet', fromMe:'Sent', fromThem:'Received',
    clearChat:'🗑 Delete chat history', clearTitle:'Delete chat history?', clearBody:'All messages with {name} will be deleted from this device. {name} keeps their copy, and files already saved to your Received files folder are not deleted.', cancel:'Cancel', del:'Delete', noMsgs:'No messages',
    reconnecting:'Connection lost. Reconnecting…', regHelp:'Enter a name for this device.<br>Others will see you by this name.',
    regPh:'e.g. My Phone', start:'Start', rename:'Rename', online:'Online', away:'Away', busy:'Busy',
    busyMute:'Busy (mute sounds)', offline:'Offline', notePh:'Set a status message', phoneBtn:'📱 Connect phone', folderBtn:'📂 Received files',
    pick:'Select someone to chat with', offNotice:'This contact is offline. Messages will be delivered when they come back online.',
    sendFile:'Send file', msgPh:'Type a message', send:'Send', phoneTitle:'Connect from your phone',
    phoneHelp:'Join the same Wi-Fi as this PC,<br>then scan the QR code or enter the address.', close:'Close', drop:'Drop files to send',
    cantConnect:'Can\'t connect.<br>Make sure LAN Chat is running.', regFail:'Registration failed: ',
    nobody:'No one here yet.<br>Run LAN Chat on another PC or<br>', nobodyDesk:'add a phone with 📱 Connect phone.', nobodyWeb:'join from another device.',
    chat:'Chat', open:'Open', showFolder:'Show in folder', save:'Save', pending:'Queued', failed:'Failed', sendFail:'Failed to send: ',
    tooBig:'File is too large', sending:'Sending…', fileFail:'File transfer failed', connErr:'connection error',
    otherAddr:'Other network address', noAddr:'No network address found. Check your Wi-Fi/LAN connection.'
  }
};
const T = k => (I18N[LANG][k] ?? I18N.en[k] ?? k);
let LOCALE, STATUS;
function applyLang(){
  LOCALE = LANG === 'ko' ? 'ko-KR' : 'en-US';
  document.documentElement.lang = LANG;
  document.querySelectorAll('[data-i18n]').forEach(el => el.textContent = T(el.dataset.i18n));
  document.querySelectorAll('[data-i18n-html]').forEach(el => el.innerHTML = T(el.dataset.i18nHtml));
  document.querySelectorAll('[data-i18n-ph]').forEach(el => el.placeholder = T(el.dataset.i18nPh));
  document.querySelectorAll('[data-i18n-title]').forEach(el => el.title = T(el.dataset.i18nTitle));
  STATUS = {online:T('online'), away:T('away'), busy:T('busy'), offline:T('offline')};
}
applyLang();
function setLang(pref, rerender){
  const next = (pref === 'ko' || pref === 'en') ? pref : SYS_LANG;
  $('#langSel').value = next;
  if (next === LANG) return;
  LANG = next; applyLang();
  if (rerender){
    renderMe(); renderContacts(); renderPeerHead(); updateTitle();
    const all = [...msgs.values()].sort((a, b) => a.ts - b.ts);
    msgs.clear(); list.innerHTML = ''; all.forEach(upsert); toBottom();
  }
}
const NATIVE = () => !!(window.pywebview && window.pywebview.api && window.pywebview.api.open_chat);

let me = null, contacts = [], urls = [], native = false;
let peer = null, peerInfo = null;
const msgs = new Map();
let stick = true;

/* ---------------------------------------------------------------- utils */
function esc(s){ return String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c])); }
function linkify(s){ return esc(s).replace(/(https?:\/\/[^\s<]+)/g, '<a href="$1" target="_blank" rel="noopener">$1</a>'); }
function fmtSize(n){ if (n < 1024) return n + ' B'; const u=['KB','MB','GB','TB']; let i=-1; do { n/=1024; i++; } while (n>=1024 && i<u.length-1); return n.toFixed(n<10?1:0)+' '+u[i]; }
function fmtTime(ts){ return new Date(ts).toLocaleTimeString(LOCALE,{hour:'numeric',minute:'2-digit'}); }
function fmtDay(ts){ return new Date(ts).toLocaleDateString(LOCALE,{year:'numeric',month:'long',day:'numeric',weekday:'long'}); }
function hue(s){ let h=0; for (const c of String(s)) h=(h*31+c.charCodeAt(0))>>>0; return h%360; }
function avatar(el, u, withDot){
  el.style.background = 'hsl('+hue(u.uid)+' 55% 52%)';
  el.innerHTML = esc((u.name||'?').trim().charAt(0).toUpperCase()) + (withDot ? '<span class="sd st-'+stKey(u)+'"></span>' : '');
}
function stKey(u){ return u.online ? (u.status||'online') : 'offline'; }
function fileIcon(m){ const t=m.mime||''; if(t.startsWith('video/'))return '🎬'; if(t.startsWith('audio/'))return '🎵';
  if(/zip|rar|7z|tar|gzip/.test(t))return '🗜️'; if(t==='application/pdf')return '📕'; if(t.startsWith('text/'))return '📝'; return '📄'; }

async function api(path, opts){
  opts = opts || {};
  opts.headers = Object.assign({}, opts.headers || {}, DESK_T ? {'X-Token': DESK_T} : {});
  if (opts.json !== undefined){ opts.body = JSON.stringify(opts.json); opts.method = opts.method || 'POST';
    opts.headers['Content-Type'] = 'application/json'; delete opts.json; }
  opts.credentials = 'same-origin';
  const r = await fetch(path, opts);
  const j = await r.json().catch(() => ({}));
  if (r.status === 401){ const e = new Error('auth'); e.auth = true; throw e; }
  if (!r.ok) throw new Error(j.error || ('HTTP ' + r.status));
  return j;
}

/* ---------------------------------------------------------------- boot */
async function boot(){
  document.body.classList.add('v-' + VIEW);
  try { start(await api('/api/init')); }
  catch (e) {
    if (e.auth && !IS_DESK) showReg();
    else { document.body.innerHTML = '<div class="empty">' + T('cantConnect') + '</div>'; }
  }
}
function showReg(){
  $('#reg').classList.remove('hidden');
  const guess = /iPhone/.test(navigator.userAgent) ? 'iPhone' : /Android/.test(navigator.userAgent) ? 'Android' : '';
  $('#regName').value = guess; $('#regName').focus();
}
$('#reg').addEventListener('submit', async e => {
  e.preventDefault();
  const name = $('#regName').value.trim();
  if (!name) return $('#regName').focus();
  try { await api('/api/register', {json:{name}}); $('#reg').classList.add('hidden'); start(await api('/api/init')); }
  catch (err) { alert(T('regFail') + err.message); }
});

function start(d){
  me = d.me; contacts = d.contacts; urls = d.urls || []; native = !!d.native;
  if (VIEW !== 'chat') $('#listPane').classList.remove('hidden');
  $('#chatPane').classList.remove('hidden');
  if (IS_DESK) $('#phoneBtn').classList.remove('hidden');
  else $('#saveLocBtn').classList.remove('hidden');
  if (!native){ $('#drawerLocBtn').dataset.i18n = 'saveLocBtn'; $('#drawerLocBtn').textContent = T('saveLocBtn'); }
  setLang(me.lang, false); applyLang();
  if (native) $('#folderBtn').classList.remove('hidden');
  renderMe(); renderContacts();
  connect();
  if (VIEW === 'chat') openHere(qs.get('peer'));
}

/* ---------------------------------------------------------------- events */
let es = null, everOpen = false;
function connect(){
  es = new EventSource('/api/events' + (DESK_T ? '?t=' + encodeURIComponent(DESK_T) : ''));
  es.onopen = () => {
    $('#connBar').classList.add('hidden');
    if (everOpen && peer) loadHistory(peer);
    everOpen = true;
  };
  es.onmessage = e => handle(JSON.parse(e.data));
  es.onerror = () => { if (everOpen) $('#connBar').classList.remove('hidden'); };
}
function handle(ev){
  if (ev.t === 'state'){
    me = ev.me; contacts = ev.contacts;
    setLang(me.lang, true);
    renderMe(); renderContacts(); renderPeerHead(); updateTitle();
  } else if (ev.t === 'cleared'){
    if (peer === ev.peer){ msgs.clear(); list.innerHTML = ''; }
  } else if (ev.t === 'msg'){
    const m = ev.m, other = m.frm === me.uid ? m.to : m.frm, incoming = m.to === me.uid && m.frm !== me.uid;
    if (peer === other){ upsert(m); if (incoming && !document.hidden) markRead(); }
    if (incoming && !IS_DESK && m.st !== undefined && (document.hidden || peer !== other)) ding();
  }
}
document.addEventListener('visibilitychange', () => { if (!document.hidden && peer) markRead(); });

/* ---------------------------------------------------------------- me */
function renderMe(){
  if (!me) return;
  avatar($('#meAv'), me, false);
  if (document.activeElement !== $('#meName')) $('#meName').value = me.name;
  if (document.activeElement !== $('#meNote')) $('#meNote').value = me.note || '';
  $('#meStatus').value = me.status || 'online';
  $('#meDot').className = 'sd st-' + (me.status || 'online');
}
function saveProfile(p){ api('/api/profile', {json:p}).catch(()=>{}); }
function bindField(el, key){
  el.addEventListener('keydown', e => { if (e.key === 'Enter' && !e.isComposing){ e.preventDefault(); el.blur(); }
    if (e.key === 'Escape'){ el.value = key === 'name' ? me.name : (me.note||''); el.blur(); } });
  el.addEventListener('blur', () => {
    const v = el.value.trim();
    if (key === 'name' && !v){ el.value = me.name; return; }
    if (v !== (me[key] || '')) saveProfile({[key]: v});
  });
}
bindField($('#meName'), 'name'); bindField($('#meNote'), 'note');
$('#langSel').addEventListener('change', e => { const v = e.target.value; setLang(v, true); saveProfile({lang: v}); });
$('#meStatus').addEventListener('change', e => { saveProfile({status: e.target.value}); $('#meDot').className = 'sd st-' + e.target.value; });

/* ---------------------------------------------------------------- contacts */
function renderContacts(){
  const box = $('#contacts');
  if (!contacts.length){
    box.innerHTML = '<div class="nobody">' + T('nobody') + (IS_DESK ? T('nobodyDesk') : T('nobodyWeb')) + '</div>';
    return;
  }
  const on = contacts.filter(c => c.online), off = contacts.filter(c => !c.online);
  let h = '';
  const row = c => '<div class="contact' + (c.online ? '' : ' off') + (c.uid === peer && VIEW === 'mobile' ? ' sel' : '') + '" data-uid="' + esc(c.uid) + '">' +
    '<div class="av" data-av="' + esc(c.uid) + '"></div><div class="ci"><div class="cn">' + esc(c.name) +
    '<span class="kind">' + (c.kind === 'mobile' ? '📱' : '💻') + '</span></div><div class="cnote">' +
    esc(c.note || STATUS[stKey(c)]) + '</div></div>' + (c.unread ? '<span class="badge">' + c.unread + '</span>' : '') + '</div>';
  if (on.length) h += '<div class="sec">' + T('online') + ' ' + on.length + '</div>' + on.map(row).join('');
  if (off.length) h += '<div class="sec">' + T('offline') + ' ' + off.length + '</div>' + off.map(row).join('');
  box.innerHTML = h;
  box.querySelectorAll('[data-av]').forEach(el => avatar(el, contacts.find(c => c.uid === el.dataset.av), true));
}
$('#contacts').addEventListener('click', e => {
  const row = e.target.closest('.contact'); if (!row) return;
  openChat(row.dataset.uid);
});
function openChat(uid){
  if (VIEW === 'mobile'){ openHere(uid, true); return; }
  if (NATIVE()) { window.pywebview.api.open_chat(uid); return; }
  window.open('/?' + new URLSearchParams({t: DESK_T, view: 'chat', peer: uid}), 'chat_' + uid, 'width=480,height=620');
}

/* ---------------------------------------------------------------- chat */
function openHere(uid, push){
  if (!uid) return;
  const changed = peer !== uid;
  peer = uid;
  peerInfo = contacts.find(c => c.uid === uid) || peerInfo;
  $('#chatEmpty').classList.add('hidden'); $('#chatMain').classList.remove('hidden');
  if (VIEW === 'mobile'){
    document.body.classList.add('in-chat');
    if (push && matchMedia('(max-width:759px)').matches) history.pushState({chat: uid}, '');
  }
  if (changed){ msgs.clear(); $('#msgs').innerHTML = ''; }
  renderPeerHead(); renderContacts();
  loadHistory(uid);
  if (!matchMedia('(pointer: coarse)').matches) $('#input').focus();
}
/* ---------------------------------------------------------------- chat menu / delete */
const chatMenu = $('#chatMenu');
$('#menuBtn').addEventListener('click', e => { e.stopPropagation(); chatMenu.classList.toggle('hidden'); });
document.addEventListener('click', e => { if (!chatMenu.contains(e.target)) chatMenu.classList.add('hidden'); });
function openDrawer(){
  chatMenu.classList.add('hidden');
  if (!peer) return;
  const files = [...msgs.values()].filter(m => m.type === 'file').sort((a, b) => b.ts - a.ts);
  const imgs = files.filter(m => /^image\/(png|jpe?g|gif|webp|bmp|avif)$/.test(m.mime || ''));
  const others = files.filter(m => !imgs.includes(m));
  let h = '';
  if (!files.length) h = '<div class="dempty">' + T('noFiles') + '</div>';
  if (imgs.length) h += '<div class="dsec">' + T('photos') + ' ' + imgs.length + '</div><div class="grid3">' +
    imgs.map(m => '<a href="/files/' + m.fid + '" target="_blank" rel="noopener" data-act="view" data-fid="' + m.fid + '"><img src="/files/' + m.fid + '" loading="lazy" alt=""></a>').join('') + '</div>';
  if (others.length) h += '<div class="dsec">' + T('filesSec') + ' ' + others.length + '</div>' +
    others.map(m => '<div class="frow"><span class="fic">' + fileIcon(m) + '</span><div class="fi"><div class="fn">' + esc(m.fname) +
      '</div><div class="fm">' + fmtSize(m.size) + ' · ' + (m.frm === me.uid ? T('fromMe') : T('fromThem')) + ' · ' + fmtDay(m.ts) + '</div>' + fileActs(m) + '</div></div>').join('');
  $('#drawerBody').innerHTML = h;
  $('#drawer').classList.remove('hidden');
}
function closeDrawer(){ $('#drawer').classList.add('hidden'); }

/* ---------------------------------------------------------------- 저장 위치 (폰) */
function platform(){
  const u = navigator.userAgent;
  if (/Android/i.test(u)) return 'android';
  if (/iPhone|iPad|iPod/.test(u) || (/Macintosh/.test(u) && navigator.maxTouchPoints > 1)) return 'ios';
  return 'desktop';
}
function browserTip(){
  const u = navigator.userAgent;
  if (/SamsungBrowser/i.test(u)) return 'tipSamsung';
  if (/Firefox|FxiOS/i.test(u)) return 'tipFirefox';
  if (/CriOS/i.test(u)) return 'tipChrome';
  if (platform() === 'ios') return 'tipSafari';
  if (/Chrome/i.test(u)) return 'tipChrome';
  return '';
}
function showSaveLocation(){
  if (native){ window.pywebview.api.open_recv_dir(); return; }   // PC 앱: 받은 파일 폴더를 바로 엶
  const pf = platform(), tip = browserTip();
  let body = '';
  if (pf !== 'desktop' && tip) body += '<div class="tipbox">' + T('tipTitle') + T(tip) + '</div>';
  body += T(pf === 'android' ? 'locAndroid' : pf === 'ios' ? 'locIOS' : 'locDesktop');
  $('#locBody').innerHTML = body;
  $('#locModal').classList.remove('hidden');
}
$('#saveLocBtn').addEventListener('click', showSaveLocation);
$('#drawerLocBtn').addEventListener('click', showSaveLocation);
$('#locClose').onclick = () => $('#locModal').classList.add('hidden');
$('#locModal').onclick = e => { if (e.target.id === 'locModal') $('#locModal').classList.add('hidden'); };
$('#filesBtn').addEventListener('click', openDrawer);
$('#drawerBack').addEventListener('click', closeDrawer);
$('#drawer').addEventListener('click', e => {
  if (e.target.id === 'drawer') return closeDrawer();
  const t = e.target.closest('[data-act]'); if (!t) return;
  if (native && NATIVE()){
    e.preventDefault();
    if (t.dataset.act === 'folder') window.pywebview.api.show_file(t.dataset.fid); else window.pywebview.api.open_file(t.dataset.fid);
  }
});

$('#clearBtn').addEventListener('click', () => {
  chatMenu.classList.add('hidden');
  if (!peer) return;
  const name = (peerInfo && peerInfo.name) || '';
  $('#confirmTitle').textContent = T('clearTitle');
  $('#confirmBody').textContent = T('clearBody').split('{name}').join(name);
  $('#confirmModal').classList.remove('hidden');
});
$('#confirmNo').onclick = () => $('#confirmModal').classList.add('hidden');
$('#confirmModal').onclick = e => { if (e.target.id === 'confirmModal') $('#confirmModal').classList.add('hidden'); };
$('#confirmYes').onclick = async () => {
  $('#confirmModal').classList.add('hidden');
  const p = peer;
  try { await api('/api/clear', {json:{peer: p}}); if (peer === p){ msgs.clear(); list.innerHTML = ''; } }
  catch (e) { alert(e.message); }
};
document.addEventListener('keydown', e => { if (e.key === 'Escape'){ chatMenu.classList.add('hidden'); $('#confirmModal').classList.add('hidden'); closeDrawer(); } });

function closeChat(){
  peer = null; document.body.classList.remove('in-chat');
  $('#chatMain').classList.add('hidden'); $('#chatEmpty').classList.remove('hidden');
  renderContacts();
}
$('#backBtn').onclick = () => { if (history.state && history.state.chat) history.back(); else closeChat(); };
window.addEventListener('popstate', () => { if (VIEW === 'mobile' && peer) closeChat(); });
if (VIEW !== 'mobile') $('#backBtn').classList.add('hidden');

async function loadHistory(uid){
  try {
    const d = await api('/api/history?peer=' + encodeURIComponent(uid));
    if (peer !== uid) return;
    if (!contacts.find(c => c.uid === uid)) peerInfo = d.peer;
    renderPeerHead();
    d.messages.forEach(upsert);
    toBottom(); markRead();
  } catch (e) {}
}
function renderPeerHead(){
  if (!peer) return;
  const u = contacts.find(c => c.uid === peer) || peerInfo || {uid: peer, name: '?', online: false};
  peerInfo = u;
  avatar($('#peerAv'), u, true);
  $('#peerName').textContent = u.name;
  $('#peerStat').textContent = STATUS[stKey(u)] + (u.note ? ' · ' + u.note : '') + (u.kind === 'mobile' ? ' · 📱' : '');
  $('#offNotice').classList.toggle('hidden', !!u.online || u.kind === 'mobile');
  if (IS_DESK) document.title = u.name + ' - ' + T('chat');
}
let readTimer = null;
function markRead(){
  if (!peer) return;
  clearTimeout(readTimer);
  const p = peer;
  readTimer = setTimeout(() => api('/api/read', {json:{peer: p}}).catch(()=>{}), 150);
}
function updateTitle(){
  if (IS_DESK) return;
  const n = contacts.reduce((a, c) => a + (c.unread || 0), 0);
  document.title = (n ? '(' + n + ') ' : '') + 'LAN Chat';
}

/* ---------------------------------------------------------------- messages */
const list = $('#msgs');
list.addEventListener('scroll', () => { stick = list.scrollHeight - list.scrollTop - list.clientHeight < 80; });
function toBottom(){ list.scrollTop = list.scrollHeight; }

function canInline(m){ const t = m.mime || ''; return (/^(image|video|audio)\//.test(t) && t !== 'image/svg+xml') || t === 'application/pdf'; }
function fileActs(m){
  if (native) return '<span class="facts"><button type="button" data-act="open" data-fid="'+m.fid+'">'+T('open')+'</button><button type="button" data-act="folder" data-fid="'+m.fid+'">'+T('showFolder')+'</button></span>';
  return '<span class="facts">' + (canInline(m) ? '<a href="/files/'+m.fid+'" target="_blank" rel="noopener">'+T('open')+'</a>' : '') +
    '<a href="/files/'+m.fid+'?dl=1" download="'+esc(m.fname)+'">'+T('save')+'</a></span>';
}
function msgEl(m){
  const mine = m.frm === me.uid;
  const el = document.createElement('div');
  el.className = 'msg' + (mine ? ' me' : '');
  el.dataset.mid = m.mid; el.dataset.ts = m.ts; el.dataset.frm = m.frm;
  let st = '';
  if (mine && m.st === 'pending') st = '<span class="st">' + T('pending') + '</span>';
  if (mine && m.st === 'failed') st = '<span class="bad">' + T('failed') + '</span>';
  const side = '<div class="side">' + st + '<span class="tm">' + fmtTime(m.ts) + '</span></div>';
  let bubble, below = '';
  if (m.type === 'file'){
    const img = /^image\/(png|jpe?g|gif|webp|bmp|avif)$/.test(m.mime || '');
    if (img){
      bubble = '<div class="bubble imgb"><img src="/files/' + m.fid + '" alt="" loading="lazy" data-act="view" data-fid="' + m.fid + '"></div>';
      below = '<div class="fline"><span>' + esc(m.fname) + ' · ' + fmtSize(m.size) + '</span>' + fileActs(m) + '</div>';
    } else {
      bubble = '<div class="bubble filebox"><span class="fic">' + fileIcon(m) + '</span><div><div class="fn">' + esc(m.fname) +
               '</div><div class="fs">' + fmtSize(m.size) + '</div>' + fileActs(m) + '</div></div>';
    }
  } else {
    bubble = '<div class="bubble">' + linkify(m.text) + '</div>';
  }
  el.innerHTML = '<div class="pav" style="background:hsl(' + hue(m.frm) + ' 55% 52%)">' + esc((m.frm_name || '?').trim().charAt(0).toUpperCase()) + '</div>' +
    '<div class="mcol"><div class="pname2">' + esc(m.frm_name || '') + '</div><div class="line">' + bubble + side + '</div>' + below + '</div>';
  el.querySelectorAll('img').forEach(i => i.addEventListener('load', () => { if (stick) toBottom(); }));
  return el;
}
/* 같은 사람이 같은 분에 연달아 보낸 메시지를 묶음: 첫 메시지에 프로필/이름, 마지막 메시지에 시간 */
function minuteKey(el){ const d = new Date(+el.dataset.ts); d.setSeconds(0, 0); return el.dataset.frm + '|' + d.getTime(); }
let regroupQueued = false;
function regroup(){
  if (regroupQueued) return;
  regroupQueued = true;
  requestAnimationFrame(() => {
    regroupQueued = false;
    const kids = [...list.children];
    kids.forEach((el, i) => {
      if (!el.classList.contains('msg')) return;
      const prev = kids[i - 1], next = kids[i + 1];
      const k = minuteKey(el);
      const samePrev = prev && prev.classList.contains('msg') && minuteKey(prev) === k;
      const sameNext = next && next.classList.contains('msg') && minuteKey(next) === k;
      el.classList.toggle('first', !samePrev);
      el.classList.toggle('last', !sameNext);
    });
  });
}
function dayKey(ts){ return new Date(ts).toDateString(); }
function upsert(m){
  const wasStick = stick;
  if (msgs.has(m.mid)){
    const old = msgs.get(m.mid);
    if (old.st && old.st !== 'pending' && m.st === 'pending') m = Object.assign({}, m, {st: old.st});
    msgs.set(m.mid, m);
    const cur = list.querySelector('[data-mid="' + m.mid + '"]');
    if (cur){ cur.replaceWith(msgEl(m)); regroup(); return; }
  }
  msgs.set(m.mid, m);
  const el = msgEl(m);
  const items = [...list.querySelectorAll('.msg')];
  const after = items.find(x => +x.dataset.ts > m.ts) || null;
  const prevMsg = after ? items[items.indexOf(after) - 1] : items[items.length - 1];
  const anchor = after || list.querySelector('.prog');
  let needSep = !prevMsg || dayKey(+prevMsg.dataset.ts) !== dayKey(m.ts);
  if (needSep && after){
    const sep = after.previousElementSibling;
    if (sep && sep.classList.contains('day') && sep.dataset.day === dayKey(m.ts)) needSep = false;
  }
  if (needSep){
    const d = document.createElement('div'); d.className = 'day'; d.dataset.day = dayKey(m.ts); d.textContent = fmtDay(m.ts);
    list.insertBefore(d, anchor);
  }
  list.insertBefore(el, anchor);
  regroup();
  if (wasStick || m.frm === me.uid) toBottom();
}
list.addEventListener('click', e => {
  const t = e.target.closest('[data-act]'); if (!t) return;
  const fid = t.dataset.fid, act = t.dataset.act;
  if (native && NATIVE()){
    e.preventDefault();
    if (act === 'folder') window.pywebview.api.show_file(fid); else window.pywebview.api.open_file(fid);
  } else if (act === 'view'){
    window.open('/files/' + fid, '_blank');
  }
});

/* ---------------------------------------------------------------- send */
const input = $('#input');
async function sendText(){
  const text = input.value;
  if (!text.trim() || !peer) return;
  input.value = ''; autosize();
  try { upsert(await api('/api/send', {json:{peer, text}})); }
  catch (e) { input.value = text; autosize(); alert(T('sendFail') + e.message); }
}
$('#form').addEventListener('submit', e => { e.preventDefault(); sendText(); if (!matchMedia('(pointer: coarse)').matches) input.focus(); });
input.addEventListener('keydown', e => {
  if (e.key === 'Enter' && !e.shiftKey && !e.isComposing && !matchMedia('(pointer: coarse)').matches){ e.preventDefault(); sendText(); }
});
function autosize(){
  input.style.height = 'auto';
  input.style.height = Math.min(input.scrollHeight, 140) + 'px';
  input.style.overflowY = input.scrollHeight > 140 ? 'auto' : 'hidden';
}
input.addEventListener('input', autosize);

function upload(file){
  if (!peer) return;
  if (file.size > MAX_UPLOAD){ alert(file.name + ': ' + T('tooBig')); return; }
  const target = peer;
  const row = document.createElement('div');
  row.className = 'prog';
  row.innerHTML = '<div>' + esc(file.name || 'file') + ' ' + T('sending') + ' <span>0%</span></div><div class="bar"><i></i></div>';
  list.appendChild(row); toBottom();
  const xhr = new XMLHttpRequest();
  xhr.open('POST', '/api/upload?peer=' + encodeURIComponent(target));
  if (DESK_T) xhr.setRequestHeader('X-Token', DESK_T);
  xhr.setRequestHeader('X-Filename', encodeURIComponent(file.name || 'file'));
  xhr.upload.onprogress = e => {
    if (!e.lengthComputable) return;
    const p = Math.round(e.loaded / e.total * 100);
    row.querySelector('span').textContent = p + '%'; row.querySelector('i').style.width = p + '%';
  };
  xhr.onload = () => { row.remove();
    if (xhr.status === 200){ const m = JSON.parse(xhr.responseText); if (peer === target) upsert(m); }
    else alert(T('fileFail') + ' (' + xhr.status + ')'); };
  xhr.onerror = () => { row.remove(); alert(T('fileFail') + ': ' + T('connErr')); };
  xhr.send(file);
}
$('#attach').onclick = () => $('#file').click();
$('#file').onchange = e => { [...e.target.files].forEach(upload); e.target.value = ''; };
document.addEventListener('paste', e => {
  if (!peer) return;
  const files = [...(e.clipboardData ? e.clipboardData.files : [])];
  if (files.length){ e.preventDefault(); files.forEach(upload); }
});
let dragDepth = 0;
document.addEventListener('dragenter', e => { if (peer && e.dataTransfer && [...e.dataTransfer.types].includes('Files')){ dragDepth++; $('#drop').classList.add('show'); } });
document.addEventListener('dragleave', () => { if (--dragDepth <= 0){ dragDepth = 0; $('#drop').classList.remove('show'); } });
document.addEventListener('dragover', e => e.preventDefault());
document.addEventListener('drop', e => { e.preventDefault(); dragDepth = 0; $('#drop').classList.remove('show');
  if (peer) [...e.dataTransfer.files].forEach(upload); });

/* ---------------------------------------------------------------- phone modal */
$('#folderBtn').onclick = () => { if (NATIVE()) window.pywebview.api.open_recv_dir(); };
$('#phoneBtn').onclick = () => {
  const box = $('#phoneList');
  box.innerHTML = urls.length ? urls.map((u, i) =>
    (i ? '<p style="margin-top:14px">' + T('otherAddr') + '</p>' : '') +
    '<img src="/api/qr?u=' + encodeURIComponent(u) + '" alt="" onerror="this.remove()"><code>' + esc(u) + '</code>').join('')
    : '<p>' + T('noAddr') + '</p>';
  $('#phoneModal').classList.remove('hidden');
};
$('#phoneClose').onclick = () => $('#phoneModal').classList.add('hidden');
$('#phoneModal').onclick = e => { if (e.target.id === 'phoneModal') $('#phoneModal').classList.add('hidden'); };

/* ---------------------------------------------------------------- sound (mobile/browser) */
let actx = null;
function unlockAudio(){ try { if (!actx) actx = new (window.AudioContext || window.webkitAudioContext)(); else if (actx.state === 'suspended') actx.resume(); } catch (e) {} }
addEventListener('pointerdown', unlockAudio); addEventListener('keydown', unlockAudio);
function ding(){
  if (!actx || (me && me.status === 'busy')) return;
  try {
    const t = actx.currentTime, o = actx.createOscillator(), g = actx.createGain();
    o.type = 'sine'; o.frequency.setValueAtTime(880, t); o.frequency.setValueAtTime(1320, t + 0.09);
    g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(0.2, t + 0.01); g.gain.exponentialRampToValueAtTime(0.0001, t + 0.3);
    o.connect(g).connect(actx.destination); o.start(t); o.stop(t + 0.32);
    if (navigator.vibrate) navigator.vibrate(80);
  } catch (e) {}
}

boot();
</script>
</body>
</html>
"""

if __name__ == "__main__":
    main()
