#!/usr/bin/env python3
"""A standalone GitHub-compatible git forge in one file (stdlib only).

One process serves four surfaces from a single in-memory store:

  * git smart HTTP   - /{owner}/{repo}.git/... (upload-pack v2, receive-pack v0)
  * REST v3          - /api/v3/...
  * GraphQL v4       - /api/graphql
  * MCP (JSON-RPC)   - /mcp

Lifecycle (the harness's, not the contest's): read MAKEFUN_ENV_URL, bind an
ephemeral port, POST {"port": N} to $MAKEFUN_ENV_URL/register, poll
$MAKEFUN_ENV_URL/done until it answers {"done": true}, then exit 0.
All state lives in memory; nothing is persisted.
"""

import base64
import hashlib
import http.client
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.parse
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# --------------------------------------------------------------------------
# Constants and environment

ZERO_OID = "0" * 40
EPOCH_BASE = 1_735_689_600  # logical clock base for forge-created commits
FORGE_IDENT = "Forge <forge@make.fun>"
JSON_CT = "application/json; charset=utf-8"

ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")

# --------------------------------------------------------------------------
# Store


class Repo:
    __slots__ = (
        "id", "owner", "name", "private", "description", "default_branch",
        "refs", "objects", "labels", "issues", "pulls",
        "next_issue", "next_pull", "next_comment",
    )

    def __init__(self, rid, owner, name, private, description):
        self.id = rid
        self.owner = owner            # None until learned from a request path
        self.name = name
        self.private = private
        self.description = description
        self.default_branch = "main"
        self.refs = {}                # full ref name -> oid hex
        self.objects = {}             # oid hex -> (type str, payload bytes)
        self.labels = {}              # name -> color
        self.issues = {}              # number -> issue dict
        self.pulls = {}               # number -> pull dict
        self.next_issue = 1
        self.next_pull = 1
        self.next_comment = 1


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.repos_by_name = {}       # name -> Repo
        self.viewer = None            # learned owner login
        self.next_repo_id = 1
        self.next_entity_id = 1       # global ids for issues / pulls / comments
        self.clock = 0                # logical clock tick for forge commits
        self.request_seq = 0          # X-GitHub-Request-Id counter

    def entity_id(self):
        eid = self.next_entity_id
        self.next_entity_id += 1
        return eid

    def tick(self):
        self.clock += 1
        return EPOCH_BASE + self.clock

    def request_id(self):
        self.request_seq += 1
        return "%012d" % self.request_seq

    def create_repo(self, name, private, description):
        """Returns the new Repo, or None when the name is taken."""
        if name in self.repos_by_name:
            return None
        repo = Repo(self.next_repo_id, self.viewer, name, private, description)
        self.next_repo_id += 1
        self.repos_by_name[name] = repo
        return repo

    def find_repo(self, owner, name):
        """Resolve (owner, name); adopts the owner on first sight of a repo.

        A repo whose recorded owner differs from the path owner is simply
        not found (the suite's rule: wrong owner is 404, never 403).
        """
        repo = self.repos_by_name.get(name)
        if repo is None:
            return None
        if repo.owner is None:
            repo.owner = owner
            if self.viewer is None:
                self.viewer = owner
        if repo.owner != owner:
            return None
        return repo


STORE = Store()

# --------------------------------------------------------------------------
# Git object layer (hand-rolled; packs carry plain objects only)

OBJ_TYPES = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}
TYPE_CODES = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}


def hash_object(otype, payload):
    head = ("%s %d\0" % (otype, len(payload))).encode()
    return hashlib.sha1(head + payload).hexdigest()


def store_object(repo, otype, payload):
    oid = hash_object(otype, payload)
    if oid not in repo.objects:
        repo.objects[oid] = (otype, payload)
    return oid


# -- commit / tree parsing (cached; objects are immutable) -----------------

_commit_cache = {}
_tree_cache = {}


def parse_commit(payload):
    """-> (tree oid, parents tuple, message bytes)"""
    head, _, message = payload.partition(b"\n\n")
    tree = None
    parents = []
    for line in head.split(b"\n"):
        if line.startswith(b"tree "):
            tree = line[5:].decode()
        elif line.startswith(b"parent "):
            parents.append(line[7:].decode())
    return tree, tuple(parents), message


def commit_info(repo, oid):
    info = _commit_cache.get(oid)
    if info is None:
        entry = repo.objects.get(oid)
        if entry is None or entry[0] != "commit":
            return None
        info = parse_commit(entry[1])
        _commit_cache[oid] = info
    return info


def parse_tree(payload):
    """-> tuple of (mode str, name str, oid hex)"""
    entries = []
    i = 0
    n = len(payload)
    while i < n:
        sp = payload.index(b" ", i)
        mode = payload[i:sp].decode()
        nul = payload.index(b"\0", sp)
        name = payload[sp + 1:nul].decode("utf-8", "surrogateescape")
        oid = payload[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        i = nul + 21
    return tuple(entries)


def tree_entries(repo, oid):
    info = _tree_cache.get(oid)
    if info is None:
        entry = repo.objects.get(oid)
        if entry is None or entry[0] != "tree":
            return ()
        info = parse_tree(entry[1])
        _tree_cache[oid] = info
    return info


def tag_target(repo, oid):
    """For a tag object: (target oid, target type). Else (None, None)."""
    entry = repo.objects.get(oid)
    if entry is None or entry[0] != "tag":
        return None, None
    target = None
    ttype = None
    for line in entry[1].split(b"\n"):
        if line.startswith(b"object "):
            target = line[7:].decode()
        elif line.startswith(b"type "):
            ttype = line[5:].decode()
        elif line == b"":
            break
    return target, ttype


def peel_to_commit(repo, oid):
    """Follow tag objects until a commit; return its oid or None."""
    seen = 0
    while oid is not None and seen < 16:
        entry = repo.objects.get(oid)
        if entry is None:
            return None
        if entry[0] == "commit":
            return oid
        if entry[0] != "tag":
            return None
        oid, _ = tag_target(repo, oid)
        seen += 1
    return None


# -- tree flatten / rebuild -------------------------------------------------

def flatten_tree(repo, tree_oid, prefix=""):
    """{path: (mode, oid)} for every blob under a tree (recursive)."""
    out = {}
    if tree_oid is None:
        return out
    for mode, name, oid in tree_entries(repo, tree_oid):
        path = prefix + name
        if mode == "40000":
            out.update(flatten_tree(repo, oid, path + "/"))
        else:
            out[path] = (mode, oid)
    return out


def _tree_sort_key(item):
    mode, name = item[0], item[1]
    return (name + "/") if mode == "40000" else name


def build_tree(repo, flat):
    """Store nested trees for {path: (mode, oid)}; return the root tree oid."""
    nested = {}
    for path, val in flat.items():
        parts = path.split("/")
        node = nested
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = val
    return _build_tree_node(repo, nested)


def _build_tree_node(repo, node):
    entries = []
    for name, val in node.items():
        if isinstance(val, dict):
            entries.append(("40000", name, _build_tree_node(repo, val)))
        else:
            entries.append((val[0], name, val[1]))
    entries.sort(key=_tree_sort_key)
    payload = b"".join(
        mode.encode() + b" " + name.encode("utf-8", "surrogateescape") + b"\0" + bytes.fromhex(oid)
        for mode, name, oid in entries
    )
    return store_object(repo, "tree", payload)


def make_commit(repo, tree_oid, parents, message, ts=None):
    if ts is None:
        ts = STORE.tick()
    ident = "%s %d +0000" % (FORGE_IDENT, ts)
    lines = ["tree %s" % tree_oid]
    for parent in parents:
        lines.append("parent %s" % parent)
    lines.append("author %s" % ident)
    lines.append("committer %s" % ident)
    payload = ("\n".join(lines) + "\n\n" + message).encode("utf-8", "surrogateescape")
    return store_object(repo, "commit", payload)


# -- history walks ------------------------------------------------------------

def commit_ancestors(repo, tip):
    """All commit oids reachable from tip (including tip), BFS order."""
    seen = []
    have = set()
    stack = [tip]
    while stack:
        oid = stack.pop()
        if oid in have:
            continue
        info = commit_info(repo, oid)
        if info is None:
            continue
        have.add(oid)
        seen.append(oid)
        stack.extend(info[1])
    return seen


def is_ancestor(repo, anc, desc):
    if anc == desc:
        return True
    seen = set()
    stack = [desc]
    while stack:
        oid = stack.pop()
        if oid == anc:
            return True
        if oid in seen:
            continue
        seen.add(oid)
        info = commit_info(repo, oid)
        if info is not None:
            stack.extend(info[1])
    return False


def merge_base(repo, a, b):
    anc_a = {}
    queue = [a]
    dist = 0
    level = [a]
    while level:
        nxt = []
        for oid in level:
            if oid in anc_a:
                continue
            anc_a[oid] = dist
            info = commit_info(repo, oid)
            if info is not None:
                nxt.extend(info[1])
        level = nxt
        dist += 1
    seen = set()
    level = [b]
    while level:
        nxt = []
        for oid in level:
            if oid in anc_a:
                return oid
            if oid in seen:
                continue
            seen.add(oid)
            info = commit_info(repo, oid)
            if info is not None:
                nxt.extend(info[1])
        level = nxt
    return None


def history_list(repo, tip):
    """Newest-first commit list from a tip (topological by discovery)."""
    out = []
    seen = set()
    stack = [tip]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        info = commit_info(repo, oid)
        if info is None:
            continue
        seen.add(oid)
        out.append(oid)
        stack.extend(reversed(info[1]))
    return out


# -- pack codec ---------------------------------------------------------------

def write_pack(objects):
    """objects: list of (otype, payload). Plain objects only. -> pack bytes"""
    out = [b"PACK", (2).to_bytes(4, "big"), len(objects).to_bytes(4, "big")]
    for otype, payload in objects:
        code = TYPE_CODES[otype]
        size = len(payload)
        first = (code << 4) | (size & 0x0F)
        size >>= 4
        header = bytearray()
        if size:
            first |= 0x80
        header.append(first)
        while size:
            byte = size & 0x7F
            size >>= 7
            if size:
                byte |= 0x80
            header.append(byte)
        out.append(bytes(header))
        out.append(zlib.compress(payload))
    body = b"".join(out)
    return body + hashlib.sha1(body).digest()


def read_pack(data, pos=0):
    """Parse a pack at data[pos:]; -> (list of (otype, payload), end pos).

    Only plain object types (1-4) occur in this suite's packs.
    """
    if data[pos:pos + 4] != b"PACK":
        raise ValueError("bad pack signature")
    count = int.from_bytes(data[pos + 8:pos + 12], "big")
    p = pos + 12
    objects = []
    for _ in range(count):
        byte = data[p]
        p += 1
        code = (byte >> 4) & 0x07
        size = byte & 0x0F
        shift = 4
        while byte & 0x80:
            byte = data[p]
            p += 1
            size |= (byte & 0x7F) << shift
            shift += 7
        if code == 6:  # ofs-delta: skip the offset varint, then fail cleanly
            byte = data[p]
            p += 1
            while byte & 0x80:
                byte = data[p]
                p += 1
            raise ValueError("delta objects are not supported")
        if code == 7:  # ref-delta: skip the base oid, then fail cleanly
            p += 20
            raise ValueError("delta objects are not supported")
        if code not in OBJ_TYPES:
            raise ValueError("unknown pack object type %d" % code)
        decomp = zlib.decompressobj()
        payload = decomp.decompress(data[p:])
        if not decomp.eof:
            raise ValueError("truncated zlib stream in pack")
        p += len(data[p:]) - len(decomp.unused_data)
        if len(payload) != size:
            raise ValueError("pack object size mismatch")
        objects.append((OBJ_TYPES[code], payload))
    return objects, p


def ingest_pack(repo, data):
    """Store every object of a pack (payloads verbatim) into the repo."""
    objects, _ = read_pack(data, 0)
    for otype, payload in objects:
        store_object(repo, otype, payload)
    return len(objects)


# -- closure engine (fetch pack semantics) ------------------------------------

def _tree_closure(repo, tree_oid, out):
    stack = [tree_oid]
    while stack:
        oid = stack.pop()
        if oid in out:
            continue
        entry = repo.objects.get(oid)
        if entry is None or entry[0] != "tree":
            continue
        out.add(oid)
        for mode, _name, child in tree_entries(repo, oid):
            if mode == "40000":
                stack.append(child)
            else:
                out.add(child)


def _closure_from(repo, root, cut_commits):
    """Full object closure of a root commit/tag. Commits in cut_commits are
    included with their trees, but their parents are not traversed."""
    out = set()
    commits = []
    oid = root
    # Resolve a tag chain at the root.
    while True:
        entry = repo.objects.get(oid)
        if entry is None:
            return out
        if entry[0] == "tag":
            out.add(oid)
            oid, _ = tag_target(repo, oid)
            if oid is None:
                return out
            continue
        break
    if entry[0] != "commit":
        out.add(oid)
        return out
    stack = [oid]
    seen = set()
    while stack:
        commit = stack.pop()
        if commit in seen:
            continue
        info = commit_info(repo, commit)
        if info is None:
            continue
        seen.add(commit)
        commits.append(commit)
        out.add(commit)
        _tree_closure(repo, info[0], out)
        if commit in cut_commits:
            continue
        stack.extend(info[1])
    return out


def compute_fetch_pack(repo, wants, haves, client_shallow, depth):
    """-> (sorted object oid list, boundary set, unshallow set)

    Object-level semantics: pack = closure(wants, depth) - closure(haves,
    cut at client_shallow). Boundary/unshallow follow the shallow rules.
    """
    excluded = set()
    excluded_commits = set()
    for have in haves:
        cut = {have} if have in client_shallow else set()
        part = _closure_from(repo, have, cut)
        excluded |= part
        for oid in part:
            entry = repo.objects.get(oid)
            if entry is not None and entry[0] == "commit":
                excluded_commits.add(oid)

    included = set()
    included_commits = set()
    tag_objects = set()
    # Level-by-level BFS from the wants (depth 1 = the wants themselves).
    level = []
    for want in wants:
        entry = repo.objects.get(want)
        if entry is None:
            continue
        if entry[0] == "tag":
            tag_objects.add(want)
            target = peel_to_commit(repo, want)
            if target is not None:
                level.append(target)
        elif entry[0] == "commit":
            level.append(want)
        else:
            included.add(want)
    current_depth = 1
    seen = set()
    frontier = level
    while frontier:
        nxt = []
        for commit in frontier:
            if commit in seen:
                continue
            seen.add(commit)
            info = commit_info(repo, commit)
            if info is None:
                continue
            included_commits.add(commit)
            included.add(commit)
            _tree_closure(repo, info[0], included)
            if depth is None or current_depth < depth:
                nxt.extend(info[1])
        frontier = nxt
        current_depth += 1
    included |= tag_objects

    pack_oids = included - excluded

    boundary = set()
    unshallow = set()
    if depth is not None:
        for commit in included_commits:
            info = commit_info(repo, commit)
            if info is None:
                continue
            for parent in info[1]:
                if parent in repo.objects and parent not in included_commits \
                        and parent not in excluded_commits:
                    boundary.add(commit)
        for shallow in client_shallow:
            if shallow in included_commits:
                info = commit_info(repo, shallow)
                if info is not None and any(p in included_commits for p in info[1]):
                    unshallow.add(shallow)
    pack_commits = {o for o in pack_oids
                    if (repo.objects.get(o) or (None,))[0] == "commit"}
    boundary &= pack_commits | included_commits
    boundary = {b for b in boundary if b in pack_oids}
    return sorted(pack_oids), boundary, unshallow


# --------------------------------------------------------------------------
# pkt-line codec

def pkt(payload):
    if isinstance(payload, str):
        payload = payload.encode()
    return ("%04x" % (len(payload) + 4)).encode() + payload


FLUSH = b"0000"
DELIM = b"0001"


def parse_pkt_lines(data, pos=0):
    """Parse pkt-lines until a flush or end of data.

    Returns (lines, pos_after_flush, special) where lines are payload bytes
    (delim packets appear as the marker b'\\x01'), special is 'flush' when a
    flush packet terminated the list.
    """
    lines = []
    n = len(data)
    while pos + 4 <= n:
        head = data[pos:pos + 4]
        try:
            length = int(head, 16)
        except ValueError:
            raise ValueError("bad pkt-line length")
        if length == 0:
            return lines, pos + 4, "flush"
        if length == 1:
            lines.append(b"\x01")
            pos += 4
            continue
        if length == 2:
            lines.append(b"\x02")
            pos += 4
            continue
        if length < 4 or pos + length > n:
            raise ValueError("pkt-line overruns body")
        lines.append(data[pos + 4:pos + length])
        pos += length
    return lines, pos, "eof"


# --------------------------------------------------------------------------
# HTTP reply helpers

def json_reply(status, obj, extra=None):
    body = json.dumps(obj, separators=(",", ":")).encode()
    headers = [("X-GitHub-Request-Id", STORE.request_id())]
    if extra:
        headers.extend(extra)
    return status, JSON_CT, body, headers


def error_reply(status, message):
    return json_reply(status, {"message": message})


def check_auth(headers):
    return headers.get("Authorization") == "Bearer " + TOKEN


# --------------------------------------------------------------------------
# Surface routers (filled in stage by stage; each returns a reply tuple)

def rest_route(method, path, query, headers, body):
    # Filled in by the REST stage; the lifecycle stage serves root + 404.
    if path in ("/api/v3", "/api/v3/"):
        if not check_auth(headers):
            return error_reply(401, "Bad credentials")
        return json_reply(200, {
            "current_user_url": "/api/v3/user",
            "rate_limit_url": "/api/v3/rate_limit",
        }, [("X-OAuth-Scopes", "repo, read:org")])
    return error_reply(404, "Not Found")


def git_route(method, segments, query, headers, body):
    return error_reply(404, "Not Found")


def graphql_route(method, path, query, headers, body):
    return error_reply(404, "Not Found")


def mcp_route(method, path, query, headers, body):
    return error_reply(404, "Not Found")


# --------------------------------------------------------------------------
# Dispatch

def route(method, raw_target, headers, body):
    raw_path, _, qs = raw_target.partition("?")
    query = urllib.parse.parse_qs(qs, keep_blank_values=True)
    path = "/".join(urllib.parse.unquote(seg) for seg in raw_path.split("/"))

    if method == "GET" and path == "/healthz":
        return 200, JSON_CT, b'{"ok":true}', []

    segments = [seg for seg in path.split("/") if seg != ""]
    if len(segments) >= 2 and segments[1].endswith(".git"):
        if not check_auth(headers):
            return error_reply(401, "Bad credentials")
        return git_route(method, segments, query, headers, body)

    if path == "/api/v3" or path.startswith("/api/v3/"):
        if not check_auth(headers):
            return error_reply(401, "Bad credentials")
        return rest_route(method, path, query, headers, body)

    if path == "/api/graphql":
        if not check_auth(headers):
            return 401, JSON_CT, b'{"message":"Bad credentials"}', \
                [("X-GitHub-Request-Id", STORE.request_id())]
        return graphql_route(method, path, query, headers, body)

    if path == "/mcp":
        if not check_auth(headers):
            return 401, JSON_CT, b'{"message":"Bad credentials"}', \
                [("X-GitHub-Request-Id", STORE.request_id())]
        return mcp_route(method, path, query, headers, body)

    return error_reply(404, "Not Found")


# --------------------------------------------------------------------------
# HTTP plumbing

class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def setup(self):
        super().setup()
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        try:
            self.connection.settimeout(120)
        except OSError:
            pass

    def log_message(self, *args):
        pass

    def send_error(self, code, message=None, explain=None):
        try:
            body = json.dumps({"message": message or "Error"}).encode()
            self.send_response(code)
            self.send_header("Content-Type", JSON_CT)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except Exception:
            pass
        self.close_connection = True

    def _read_body(self):
        length = self.headers.get("Content-Length")
        if length is not None:
            n = int(length)
            return self.rfile.read(n) if n > 0 else b""
        if (self.headers.get("Transfer-Encoding") or "").lower() == "chunked":
            chunks = []
            while True:
                line = self.rfile.readline(65536).strip()
                size = int(line.split(b";")[0], 16)
                if size == 0:
                    # trailers until an empty line
                    while True:
                        trailer = self.rfile.readline(65536)
                        if trailer in (b"\r\n", b"\n", b""):
                            break
                    break
                chunks.append(self.rfile.read(size))
                self.rfile.read(2)
            return b"".join(chunks)
        return b""

    def _handle(self):
        try:
            body = self._read_body()
            with STORE.lock:
                status, ctype, payload, extra = route(self.command, self.path, self.headers, body)
        except Exception:
            status, ctype, payload, extra = 500, JSON_CT, \
                b'{"message":"Internal Server Error"}', []
        try:
            self.send_response(status)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(payload)))
            for key, value in extra:
                self.send_header(key, value)
            self.end_headers()
            if payload and self.command != "HEAD":
                self.wfile.write(payload)
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True

    do_GET = _handle
    do_POST = _handle
    do_PUT = _handle
    do_PATCH = _handle
    do_DELETE = _handle
    do_HEAD = _handle


class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 128
    allow_reuse_address = True


# --------------------------------------------------------------------------
# Lifecycle (translated from the starter: register, poll /done, exit 0)

REQUEST_TIMEOUT = 30.0
RETRY_INITIAL = 0.250
RETRY_MAX = 2.000


def _retry_delay(attempt):
    return min(RETRY_MAX, RETRY_INITIAL * (2 ** min(attempt, 8)))


def _env_request(method, path, payload=None):
    parts = urllib.parse.urlsplit(ENV_URL)
    if parts.scheme == "https":
        conn = http.client.HTTPSConnection(parts.hostname, parts.port or 443,
                                           timeout=REQUEST_TIMEOUT)
    else:
        conn = http.client.HTTPConnection(parts.hostname, parts.port or 80,
                                          timeout=REQUEST_TIMEOUT)
    try:
        body = None
        headers = {}
        if payload is not None:
            body = json.dumps(payload).encode()
            headers["Content-Type"] = "application/json"
        conn.request(method, path, body=body, headers=headers)
        resp = conn.getresponse()
        data = resp.read()
        return resp.status, data
    finally:
        conn.close()


def register(port):
    attempt = 0
    while True:
        try:
            status, _ = _env_request("POST", "/register", {"port": port})
            if status in (200, 409):
                return
            if status in (400, 405):
                sys.stderr.write("[entry] register answered HTTP %d\n" % status)
                sys.exit(1)
        except SystemExit:
            raise
        except Exception:
            pass
        time.sleep(_retry_delay(attempt))
        attempt += 1


def wait_for_done():
    attempt = 0
    while True:
        try:
            status, data = _env_request("GET", "/done")
            if status == 200:
                try:
                    if json.loads(data.decode() or "{}").get("done") is True:
                        return
                except ValueError:
                    pass
        except Exception:
            pass
        time.sleep(_retry_delay(attempt))
        attempt += 1


def main():
    if not ENV_URL:
        sys.stderr.write("[entry] MAKEFUN_ENV_URL is not set: "
                         "there is no env to register with\n")
        sys.exit(1)
    server = ForgeServer(("", 0), ForgeHandler)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    sys.stdout.write("[entry] listening on port %d\n" % port)
    sys.stdout.flush()
    register(port)
    sys.stdout.write("[entry] registered; waiting for the env to say done\n")
    sys.stdout.flush()
    wait_for_done()
    server.shutdown()
    server.server_close()
    sys.stdout.write("[entry] done\n")
    sys.stdout.flush()
    sys.exit(0)


if __name__ == "__main__":
    main()
