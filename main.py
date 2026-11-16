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
import datetime
import difflib
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

def repo_json(repo):
    owner = repo.owner or STORE.viewer or ""
    return {
        "id": repo.id,
        "name": repo.name,
        "full_name": "%s/%s" % (owner, repo.name),
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "owner": {"login": owner},
    }


def issue_json(issue):
    return {
        "id": issue["id"],
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "labels": [{"name": name} for name in issue["labels"]],
    }


def pull_json(repo, pull):
    head_sha = repo.refs.get("refs/heads/" + pull["head"], "")
    base_sha = repo.refs.get("refs/heads/" + pull["base"], "")
    obj = {
        "id": pull["id"],
        "number": pull["number"],
        "state": pull["state"],
        "title": pull["title"],
        "body": pull["body"],
        "head": {"ref": pull["head"], "sha": head_sha},
        "base": {"ref": pull["base"], "sha": base_sha},
        "merged": pull["merged"],
    }
    if pull["merged"]:
        obj["merged_at"] = pull["merged_at"]
        obj["merge_commit_sha"] = pull["merge_commit_sha"]
    return obj


def resolve_ref(repo, ref):
    """Branch name, full ref, tag name or commit sha -> commit oid or None."""
    if ref is None:
        ref = repo.default_branch
    if ref in repo.refs:
        target = repo.refs[ref]
        return peel_to_commit(repo, target) or target
    for prefix in ("refs/heads/", "refs/tags/"):
        if prefix + ref in repo.refs:
            return peel_to_commit(repo, repo.refs[prefix + ref])
    if len(ref) == 40 and commit_info(repo, ref) is not None:
        return ref
    return None


def flat_at(repo, commit_oid):
    if commit_oid is None:
        return {}
    info = commit_info(repo, commit_oid)
    if info is None:
        return {}
    return flatten_tree(repo, info[0])


def iso_now():
    ts = EPOCH_BASE + STORE.clock
    moment = datetime.datetime.fromtimestamp(ts, datetime.timezone.utc)
    return moment.strftime("%Y-%m-%dT%H:%M:%SZ")


def squash_merge(repo, pull):
    """File-level 3-way squash merge (§B.4). -> (ok, conflict, commit oid)"""
    base_tip = repo.refs.get("refs/heads/" + pull["base"])
    head_tip = repo.refs.get("refs/heads/" + pull["head"])
    if base_tip is None or head_tip is None:
        return False, True, None
    base_commit = peel_to_commit(repo, base_tip) or base_tip
    head_commit = peel_to_commit(repo, head_tip) or head_tip
    mb = merge_base(repo, base_commit, head_commit)
    mb_flat = flat_at(repo, mb)
    base_flat = flat_at(repo, base_commit)
    head_flat = flat_at(repo, head_commit)
    merged = dict(base_flat)
    paths = set(mb_flat) | set(base_flat) | set(head_flat)
    for path in paths:
        before = mb_flat.get(path)
        current = base_flat.get(path)
        incoming = head_flat.get(path)
        if incoming != before and current == before:
            if incoming is None:
                merged.pop(path, None)
            else:
                merged[path] = incoming
        elif current != before and incoming == before:
            pass
        elif incoming == current:
            pass
        else:
            return False, True, None
    tree_oid = build_tree(repo, merged)
    message = pull["title"]
    if pull["body"]:
        message = message + "\n\n" + pull["body"]
    commit = make_commit(repo, tree_oid, [base_commit], message)
    repo.refs["refs/heads/" + pull["base"]] = commit
    return True, False, commit


def pull_files(repo, pull):
    """Changed paths between the merge-base and the head tip, with counts."""
    base_tip = repo.refs.get("refs/heads/" + pull["base"])
    head_tip = repo.refs.get("refs/heads/" + pull["head"])
    if base_tip is None or head_tip is None:
        return []
    base_commit = peel_to_commit(repo, base_tip) or base_tip
    head_commit = peel_to_commit(repo, head_tip) or head_tip
    mb = merge_base(repo, base_commit, head_commit)
    base_flat = flat_at(repo, mb)
    head_flat = flat_at(repo, head_commit)
    out = []
    for path in sorted(set(base_flat) | set(head_flat)):
        before = base_flat.get(path)
        after = head_flat.get(path)
        if before == after:
            continue
        if before is None:
            status = "added"
        elif after is None:
            status = "removed"
        else:
            status = "modified"
        before_lines = _blob_lines(repo, before)
        after_lines = _blob_lines(repo, after)
        additions = deletions = 0
        matcher = difflib.SequenceMatcher(None, before_lines, after_lines, autojunk=False)
        for op, i1, i2, j1, j2 in matcher.get_opcodes():
            if op in ("replace", "delete"):
                deletions += i2 - i1
            if op in ("replace", "insert"):
                additions += j2 - j1
        out.append({
            "filename": path,
            "status": status,
            "additions": additions,
            "deletions": deletions,
            "changes": additions + deletions,
        })
    return out


def _blob_lines(repo, flat_entry):
    if flat_entry is None:
        return []
    entry = repo.objects.get(flat_entry[1])
    if entry is None:
        return []
    return entry[1].decode("utf-8", "replace").splitlines()


def _parse_body(body):
    """-> (dict, error reply or None). Empty body parses as {}."""
    if not body:
        return {}, None
    try:
        data = json.loads(body.decode("utf-8"))
    except (ValueError, UnicodeDecodeError):
        return None, error_reply(400, "Problems parsing JSON")
    if not isinstance(data, dict):
        return None, error_reply(400, "Problems parsing JSON")
    return data, None


def _q1(query, name, default=None):
    values = query.get(name)
    return values[0] if values else default


def _page_params(query):
    try:
        per_page = int(_q1(query, "per_page", "30"))
    except ValueError:
        per_page = 30
    try:
        page = int(_q1(query, "page", "1"))
    except ValueError:
        page = 1
    return max(1, per_page), max(1, page)


def rest_route(method, path, query, headers, body):
    if path in ("/api/v3", "/api/v3/"):
        return json_reply(200, {
            "current_user_url": "/api/v3/user",
            "rate_limit_url": "/api/v3/rate_limit",
        }, [("X-OAuth-Scopes", "repo, read:org")])
    if path == "/api/v3/meta" and method == "GET":
        return json_reply(200, {"installed_version": "1.0.0"})
    if path == "/api/v3/user" and method == "GET":
        return json_reply(200, {"login": STORE.viewer or ""})
    if path == "/api/v3/user/repos":
        if method == "POST":
            return _create_repo(body)
        if method == "GET":
            return _list_user_repos(query, headers)

    parts = [seg for seg in path.split("/") if seg != ""]
    # parts: ['api', 'v3', 'repos', owner, name, ...]
    if len(parts) >= 5 and parts[0] == "api" and parts[1] == "v3" and parts[2] == "repos":
        owner, name = parts[3], parts[4]
        repo = STORE.find_repo(owner, name)
        if repo is None:
            return error_reply(404, "Not Found")
        tail = parts[5:]
        return _repo_route(repo, method, tail, query, body)
    return error_reply(404, "Not Found")


def _create_repo(body):
    data, err = _parse_body(body)
    if err is not None:
        return err
    name = data.get("name")
    if not isinstance(name, str) or not name:
        return error_reply(422, "name is required")
    repo = STORE.create_repo(name, bool(data.get("private", False)),
                             data.get("description") or "")
    if repo is None:
        return error_reply(422, "name already exists on this account")
    return json_reply(201, repo_json(repo))


def _list_user_repos(query, headers):
    per_page, page = _page_params(query)
    repos = [STORE.repos_by_name[name] for name in
             sorted(STORE.repos_by_name, key=lambda n: STORE.repos_by_name[n].id)]
    repos = [r for r in repos if r.owner is None or STORE.viewer is None
             or r.owner == STORE.viewer]
    total = len(repos)
    start = (page - 1) * per_page
    chunk = repos[start:start + per_page]
    extra = []
    if start + per_page < total:
        host = headers.get("Host", "127.0.0.1")
        base = "http://%s/api/v3/user/repos" % host
        links = ['<%s?per_page=%d&page=%d>; rel="next"' % (base, per_page, page + 1),
                 '<%s?per_page=%d&page=%d>; rel="last"' % (
                     base, per_page, max(1, (total + per_page - 1) // per_page))]
        extra.append(("Link", ", ".join(links)))
    return json_reply(200, [repo_json(r) for r in chunk], extra)


def _repo_route(repo, method, tail, query, body):
    if not tail:
        if method == "GET":
            return json_reply(200, repo_json(repo))
        if method == "PATCH":
            data, err = _parse_body(body)
            if err is not None:
                return err
            if "description" in data:
                repo.description = data["description"] or ""
            if "private" in data:
                repo.private = bool(data["private"])
            return json_reply(200, repo_json(repo))
        if method == "DELETE":
            del STORE.repos_by_name[repo.name]
            return 204, JSON_CT, b"", [("X-GitHub-Request-Id", STORE.request_id())]
        return error_reply(404, "Not Found")

    if tail[0] == "git" and len(tail) >= 2 and tail[1] == "refs":
        if method == "POST" and len(tail) == 2:
            return _create_ref(repo, body)
        if method == "GET" and len(tail) >= 4 and tail[2] == "heads":
            branch = "/".join(tail[3:])
            sha = repo.refs.get("refs/heads/" + branch)
            if sha is None:
                return error_reply(404, "Not Found")
            return json_reply(200, {"ref": "refs/heads/" + branch,
                                    "object": {"sha": sha, "type": "commit"}})
        return error_reply(404, "Not Found")

    if tail[0] == "branches":
        if method == "GET" and len(tail) == 1:
            out = []
            for ref in sorted(repo.refs):
                if ref.startswith("refs/heads/"):
                    out.append({"name": ref[len("refs/heads/"):],
                                "commit": {"sha": repo.refs[ref]}})
            return json_reply(200, out)
        if method == "GET" and len(tail) >= 2:
            branch = "/".join(tail[1:])
            sha = repo.refs.get("refs/heads/" + branch)
            if sha is None:
                return error_reply(404, "Not Found")
            return json_reply(200, {"name": branch, "commit": {"sha": sha}})
        return error_reply(404, "Not Found")

    if tail[0] == "commits" and len(tail) == 1 and method == "GET":
        tip = resolve_ref(repo, _q1(query, "sha"))
        if tip is None:
            return json_reply(200, [])
        out = []
        for oid in history_list(repo, tip):
            info = commit_info(repo, oid)
            message = info[2].decode("utf-8", "replace") if info else ""
            out.append({"sha": oid, "commit": {"message": message}})
        return json_reply(200, out)

    if tail[0] == "contents" and len(tail) >= 2:
        cpath = "/".join(tail[1:])
        if method == "PUT":
            return _contents_put(repo, cpath, body)
        if method == "GET":
            return _contents_get(repo, cpath, _q1(query, "ref"))
        if method == "DELETE":
            return _contents_delete(repo, cpath, body)
        return error_reply(404, "Not Found")

    if tail[0] == "labels" and len(tail) == 1 and method == "POST":
        data, err = _parse_body(body)
        if err is not None:
            return err
        lname = data.get("name")
        if not isinstance(lname, str) or not lname:
            return error_reply(422, "name is required")
        repo.labels[lname] = data.get("color") or ""
        return json_reply(201, {"name": lname, "color": repo.labels[lname]})

    if tail[0] == "issues":
        return _issues_route(repo, method, tail[1:], query, body)

    if tail[0] == "pulls":
        return _pulls_route(repo, method, tail[1:], query, body)

    return error_reply(404, "Not Found")


def _create_ref(repo, body):
    data, err = _parse_body(body)
    if err is not None:
        return err
    ref = data.get("ref")
    sha = data.get("sha")
    if not isinstance(ref, str) or not ref.startswith("refs/"):
        return error_reply(422, "ref is invalid")
    if not isinstance(sha, str) or commit_info(repo, sha) is None:
        return error_reply(422, "sha is not a commit in this repository")
    if ref in repo.refs:
        return error_reply(422, "Reference already exists")
    repo.refs[ref] = sha
    return json_reply(201, {"ref": ref, "object": {"sha": sha, "type": "commit"}})


def _contents_put(repo, cpath, body):
    data, err = _parse_body(body)
    if err is not None:
        return err
    try:
        raw = base64.b64decode(data.get("content") or "", validate=False)
    except (ValueError, TypeError):
        return error_reply(422, "content is not valid base64")
    branch = data.get("branch") or repo.default_branch
    tip = repo.refs.get("refs/heads/" + branch)
    if tip is None and branch != repo.default_branch:
        tip = repo.refs.get("refs/heads/" + repo.default_branch)
    tip_commit = peel_to_commit(repo, tip) if tip else None
    flat = flat_at(repo, tip_commit)
    existing = flat.get(cpath)
    sha_given = data.get("sha")
    if existing is not None and sha_given is not None \
            and str(sha_given).lower() != existing[1].lower():
        return error_reply(409, "sha does not match the current content")
    blob_oid = store_object(repo, "blob", raw)
    flat[cpath] = ("100644", blob_oid)
    tree_oid = build_tree(repo, flat)
    parents = [tip_commit] if tip_commit else []
    commit = make_commit(repo, tree_oid, parents, data.get("message") or "")
    repo.refs["refs/heads/" + branch] = commit
    status = 201 if existing is None else 200
    return json_reply(status, {
        "content": {"name": cpath.split("/")[-1], "path": cpath,
                    "sha": blob_oid, "encoding": "base64"},
        "commit": {"sha": commit},
    })


def _contents_get(repo, cpath, ref):
    tip = resolve_ref(repo, ref)
    if tip is None:
        return error_reply(404, "Not Found")
    info = commit_info(repo, tip)
    if info is None:
        return error_reply(404, "Not Found")
    node = info[0]
    parts = [p for p in cpath.split("/") if p != ""]
    for depth, part in enumerate(parts):
        entries = tree_entries(repo, node)
        found = None
        for mode, name, oid in entries:
            if name == part:
                found = (mode, oid)
                break
        if found is None:
            return error_reply(404, "Not Found")
        mode, oid = found
        if depth == len(parts) - 1:
            if mode == "40000":
                return json_reply(200, _dir_listing(repo, oid, cpath))
            entry = repo.objects.get(oid)
            payload = entry[1] if entry else b""
            return json_reply(200, {
                "type": "file",
                "encoding": "base64",
                "content": base64.b64encode(payload).decode(),
                "sha": oid,
                "size": len(payload),
                "name": part,
                "path": cpath,
            })
        if mode != "40000":
            return error_reply(404, "Not Found")
        node = oid
    return json_reply(200, _dir_listing(repo, node, cpath))


def _dir_listing(repo, tree_oid, cpath):
    out = []
    for mode, name, oid in tree_entries(repo, tree_oid):
        child_path = (cpath.rstrip("/") + "/" + name) if cpath else name
        out.append({
            "type": "dir" if mode == "40000" else "file",
            "name": name,
            "path": child_path,
            "sha": oid,
        })
    return out


def _contents_delete(repo, cpath, body):
    data, err = _parse_body(body)
    if err is not None:
        return err
    branch = data.get("branch") or repo.default_branch
    tip = repo.refs.get("refs/heads/" + branch)
    tip_commit = peel_to_commit(repo, tip) if tip else None
    flat = flat_at(repo, tip_commit)
    existing = flat.get(cpath)
    if existing is None:
        return error_reply(404, "Not Found")
    sha_given = data.get("sha")
    if sha_given is not None and str(sha_given).lower() != existing[1].lower():
        return error_reply(409, "sha does not match the current content")
    del flat[cpath]
    tree_oid = build_tree(repo, flat)
    parents = [tip_commit] if tip_commit else []
    commit = make_commit(repo, tree_oid, parents, data.get("message") or "")
    repo.refs["refs/heads/" + branch] = commit
    return json_reply(200, {"commit": {"sha": commit}, "content": None})


def _issues_route(repo, method, tail, query, body):
    if not tail:
        if method == "POST":
            data, err = _parse_body(body)
            if err is not None:
                return err
            labels = data.get("labels") or []
            for lname in labels:
                if lname not in repo.labels:
                    return error_reply(422, "label %s does not exist" % lname)
            number = repo.next_issue
            repo.next_issue += 1
            issue = {
                "id": STORE.entity_id(),
                "number": number,
                "title": data.get("title") or "",
                "body": data.get("body") or "",
                "state": "open",
                "labels": list(labels),
                "comments": [],
            }
            repo.issues[number] = issue
            return json_reply(201, issue_json(issue))
        if method == "GET":
            state = _q1(query, "state", "open")
            items = [i for i in repo.issues.values()
                     if state == "all" or i["state"] == state]
            direction = _q1(query, "direction", "desc")
            items.sort(key=lambda i: i["number"], reverse=(direction != "asc"))
            per_page, page = _page_params(query)
            start = (page - 1) * per_page
            return json_reply(200, [issue_json(i) for i in items[start:start + per_page]])
        return error_reply(404, "Not Found")

    if not tail[0].isdigit():
        return error_reply(404, "Not Found")
    number = int(tail[0])
    issue = repo.issues.get(number)
    if issue is None:
        return error_reply(404, "Not Found")
    if len(tail) == 1:
        if method == "GET":
            return json_reply(200, issue_json(issue))
        if method == "PATCH":
            data, err = _parse_body(body)
            if err is not None:
                return err
            if data.get("state") in ("open", "closed"):
                issue["state"] = data["state"]
            if "title" in data:
                issue["title"] = data["title"] or ""
            if "body" in data:
                issue["body"] = data["body"] or ""
            return json_reply(200, issue_json(issue))
        return error_reply(404, "Not Found")
    if len(tail) == 2 and tail[1] == "comments":
        if method == "POST":
            data, err = _parse_body(body)
            if err is not None:
                return err
            comment = {"id": STORE.entity_id(), "body": data.get("body") or ""}
            issue["comments"].append(comment)
            return json_reply(201, dict(comment))
        if method == "GET":
            return json_reply(200, [dict(c) for c in issue["comments"]])
    return error_reply(404, "Not Found")


def _pulls_route(repo, method, tail, query, body):
    if not tail:
        if method == "POST":
            data, err = _parse_body(body)
            if err is not None:
                return err
            head = data.get("head")
            base = data.get("base")
            if not isinstance(head, str) or not isinstance(base, str):
                return error_reply(422, "head and base are required")
            if "refs/heads/" + head not in repo.refs:
                return error_reply(422, "head branch does not exist")
            if "refs/heads/" + base not in repo.refs:
                return error_reply(422, "base branch does not exist")
            for pull in repo.pulls.values():
                if pull["state"] == "open" and pull["head"] == head \
                        and pull["base"] == base:
                    return error_reply(422, "A pull request already exists "
                                            "for this head and base")
            number = repo.next_pull
            repo.next_pull += 1
            pull = {
                "id": STORE.entity_id(),
                "number": number,
                "title": data.get("title") or "",
                "body": data.get("body") or "",
                "state": "open",
                "head": head,
                "base": base,
                "merged": False,
                "merged_at": None,
                "merge_commit_sha": None,
            }
            repo.pulls[number] = pull
            return json_reply(201, pull_json(repo, pull))
        if method == "GET":
            state = _q1(query, "state", "open")
            items = [p for p in repo.pulls.values()
                     if state == "all" or p["state"] == state]
            items.sort(key=lambda p: p["number"], reverse=True)
            per_page, page = _page_params(query)
            start = (page - 1) * per_page
            return json_reply(200, [pull_json(repo, p)
                                    for p in items[start:start + per_page]])
        return error_reply(404, "Not Found")

    if not tail[0].isdigit():
        return error_reply(404, "Not Found")
    number = int(tail[0])
    pull = repo.pulls.get(number)
    if len(tail) == 1 and method == "GET":
        if pull is None:
            return error_reply(404, "Not Found")
        return json_reply(200, pull_json(repo, pull))
    if pull is None:
        return error_reply(404, "Not Found")
    if len(tail) == 2 and tail[1] == "files" and method == "GET":
        return json_reply(200, pull_files(repo, pull))
    if len(tail) == 2 and tail[1] == "merge" and method == "PUT":
        data, err = _parse_body(body)
        if err is not None:
            return err
        if pull["state"] == "closed":
            return error_reply(405, "Pull Request is not mergeable")
        ok, conflict, commit = squash_merge(repo, pull)
        if conflict:
            return error_reply(405, "Pull Request is not mergeable")
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merged_at"] = iso_now()
        pull["merge_commit_sha"] = commit
        return json_reply(200, {"sha": commit, "merged": True,
                                "message": "Pull Request successfully merged"})
    return error_reply(404, "Not Found")


# --------------------------------------------------------------------------
# Git smart HTTP

GIT_ZERO = "0" * 40
UPLOAD_CAPS_V0 = "side-band-64k thin-pack ofs-delta symref=HEAD:refs/heads/main"
RECEIVE_CAPS_V0 = "report-status side-band-64k delete-refs ofs-delta"


def _bin_reply(status, ctype, body):
    return status, ctype, body, []


def _git_advertisement(repo, service, version2):
    if service == "git-upload-pack" and version2:
        out = pkt(b"# service=git-upload-pack\n") + FLUSH
        out += pkt(b"version 2\n")
        out += pkt(b"ls-refs=unborn\n")
        out += pkt(b"fetch=shallow\n")
        out += pkt(b"object-format=sha1\n")
        return out + FLUSH
    caps = UPLOAD_CAPS_V0 if service == "git-upload-pack" else RECEIVE_CAPS_V0
    out = pkt(("# service=%s\n" % service).encode()) + FLUSH
    if not repo.refs:
        return out + pkt(("%s capabilities^{}\0%s\n" % (GIT_ZERO, caps)).encode()) + FLUSH
    lines = [("HEAD", repo.refs.get("refs/heads/main"))]
    for name in sorted(repo.refs):
        oid = repo.refs[name]
        lines.append((name, oid))
        entry = repo.objects.get(oid)
        if entry is not None and entry[0] == "tag":
            commit = peel_to_commit(repo, oid)
            if commit is not None:
                lines.append((name + "^{}", commit))
    for index, (name, oid) in enumerate(lines):
        line = "%s %s" % (oid if oid else GIT_ZERO, name)
        if index == 0:
            line += "\0" + caps
        out += pkt((line + "\n").encode())
    return out + FLUSH


def _git_ls_refs(repo, args):
    prefixes = [a.split(" ", 1)[1] for a in args if a.startswith("ref-prefix ")]
    want_peel = "peel" in args
    want_symrefs = "symrefs" in args
    want_unborn = "unborn" in args

    def matches(name):
        return not prefixes or any(name.startswith(p) for p in prefixes)

    out = b""
    main_tip = repo.refs.get("refs/heads/main")
    if matches("HEAD"):
        suffix = " symref-target:refs/heads/main" if want_symrefs else ""
        if main_tip is not None:
            out += pkt(("%s HEAD%s\n" % (main_tip, suffix)).encode())
        elif want_unborn:
            out += pkt(("unborn HEAD%s\n" % suffix).encode())
        else:
            out += pkt(("%s HEAD%s\n" % (GIT_ZERO, suffix)).encode())
    for name in sorted(repo.refs):
        if not matches(name):
            continue
        oid = repo.refs[name]
        line = "%s %s" % (oid, name)
        entry = repo.objects.get(oid)
        if want_peel and entry is not None and entry[0] == "tag":
            commit = peel_to_commit(repo, oid)
            if commit is not None:
                line += " peeled:%s" % commit
        out += pkt((line + "\n").encode())
    return out + FLUSH


def _git_fetch(repo, args):
    wants, haves, client_shallow = [], [], []
    depth = None
    for arg in args:
        if arg.startswith("want "):
            wants.append(arg[5:])
        elif arg.startswith("have "):
            haves.append(arg[5:])
        elif arg.startswith("shallow "):
            client_shallow.append(arg[8:])
        elif arg.startswith("deepen "):
            try:
                depth = int(arg[7:])
            except ValueError:
                pass
    pack_oids, boundary, unshallow = compute_fetch_pack(
        repo, wants, haves, client_shallow, depth)
    pack = write_pack([repo.objects[oid] for oid in pack_oids])
    out = b""
    if boundary or unshallow:
        out += pkt(b"shallow-info\n")
        for oid in sorted(boundary):
            out += pkt(("shallow %s\n" % oid).encode())
        for oid in sorted(unshallow):
            out += pkt(("unshallow %s\n" % oid).encode())
        out += FLUSH
    out += pkt(b"packfile\n")
    for offset in range(0, len(pack), 60000):
        out += pkt(b"\x01" + pack[offset:offset + 60000])
    return out + FLUSH


def _git_receive_pack(repo, body):
    try:
        lines, pos, special = parse_pkt_lines(body or b"")
    except ValueError:
        lines, pos, special = [], 0, "eof"
    pack_data = body[pos:] if special == "flush" else b""
    commands = []
    client_caps = ""
    for index, raw in enumerate(lines):
        line = raw.decode("utf-8", "replace").rstrip("\n")
        if index == 0 and "\0" in line:
            line, client_caps = line.split("\0", 1)
        parts = line.split(" ")
        if len(parts) == 3 and len(parts[0]) == 40 and len(parts[1]) == 40:
            commands.append((parts[0], parts[1], parts[2]))
    unpack_ok = True
    if pack_data:
        try:
            ingest_pack(repo, pack_data)
        except Exception:
            unpack_ok = False
    results = []
    for old, new, ref in commands:
        current = repo.refs.get(ref)
        reason = None
        if not unpack_ok:
            reason = "unpack failed"
        elif new == GIT_ZERO:  # delete
            if current is None:
                reason = "reference does not exist"
            elif old != GIT_ZERO and current != old:
                reason = "stale ref"
        elif old == GIT_ZERO:  # create
            if current is not None:
                reason = "already exists"
            elif new not in repo.objects:
                reason = "missing object"
        else:  # update
            if current != old:
                reason = "stale ref"
            elif new not in repo.objects:
                reason = "missing object"
            elif not ref.startswith("refs/tags/") and new != current:
                info = commit_info(repo, new)
                fast = info is not None and (
                    current in info[1] or is_ancestor(repo, current, new))
                if not fast:
                    reason = "non-fast-forward"
        if reason is None:
            if new == GIT_ZERO:
                repo.refs.pop(ref, None)
            else:
                repo.refs[ref] = new
            results.append("ok %s\n" % ref)
        else:
            results.append("ng %s %s\n" % (ref, reason))
    report = [("unpack ok\n" if unpack_ok else "unpack error\n")] + results
    sideband = "side-band-64k" in client_caps.split(" ")
    out = b""
    for line in report:
        encoded = pkt(line.encode())
        out += pkt(b"\x01" + encoded) if sideband else encoded
    return out + FLUSH


def _v2_args(lines):
    """Split a v2 command request into (command, args after the delim)."""
    if not lines:
        return None, []
    first = lines[0].decode("utf-8", "replace").rstrip("\n")
    if not first.startswith("command="):
        return None, []
    args = []
    seen_delim = False
    for raw in lines[1:]:
        if raw == b"\x01":
            seen_delim = True
            continue
        if seen_delim:
            args.append(raw.decode("utf-8", "replace").rstrip("\n"))
    return first[len("command="):], args


def git_route(method, segments, query, headers, body):
    owner = segments[0]
    name = segments[1][:-len(".git")]
    repo = STORE.find_repo(owner, name)
    if repo is None:
        return error_reply(404, "Not Found")
    rest = segments[2:]
    if rest == ["info", "refs"] and method == "GET":
        service = _q1(query, "service", "")
        if service not in ("git-upload-pack", "git-receive-pack"):
            return error_reply(404, "Not Found")
        version2 = headers.get("Git-Protocol") == "version=2"
        return _bin_reply(200, "application/x-%s-advertisement" % service,
                          _git_advertisement(repo, service, version2))
    if rest == ["git-upload-pack"] and method == "POST":
        try:
            lines, _pos, _special = parse_pkt_lines(body or b"")
        except ValueError:
            return _bin_reply(400, "text/plain", b"malformed pkt-line\n")
        command, args = _v2_args(lines)
        if command == "ls-refs":
            return _bin_reply(200, "application/x-git-upload-pack-result",
                              _git_ls_refs(repo, args))
        if command == "fetch":
            return _bin_reply(200, "application/x-git-upload-pack-result",
                              _git_fetch(repo, args))
        return _bin_reply(400, "text/plain", b"unknown command\n")
    if rest == ["git-receive-pack"] and method == "POST":
        return _bin_reply(200, "application/x-git-receive-pack-result",
                          _git_receive_pack(repo, body or b""))
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
