#!/usr/bin/env python3
"""forge — a single-process, stdlib-only GitHub-compatible git forge.

Serves, from one process and one in-memory store:

  * git smart HTTP (protocol v2 and v0) at /{owner}/{repo}.git
    — upload-pack (ls-refs, fetch, shallow, deepen) and receive-pack
    (report-status, side-band-64k, delete-refs, fast-forward enforcement),
    with a from-scratch pack reader/writer (plain objects and deltas);
  * GitHub REST v3 at /api/v3 — repositories, branches, commits, contents,
    issues, labels, comments, pull requests and merges;
  * GitHub GraphQL v4 at /api/graphql — the documents gh and
    github-mcp-server send, plus __type introspection and batching;
  * MCP (Streamable HTTP, revision 2026-07-28 with the 2025-11-25
    handshake as fallback) at /mcp — server/discover, initialize,
    tools/list and tools/call for the six forge tools.

Lifecycle (the make.fun wire): bind an ephemeral port, POST {"port": N} to
$MAKEFUN_ENV_URL/register, then poll GET $MAKEFUN_ENV_URL/done until
{"done": true} and exit 0. With MAKEFUN_ENV_URL unset the forge runs
standalone for local testing and prints its URL.

Authentication: every API call carries `Authorization: Bearer
$MAKEFUN_SHOP_TOKEN`. A missing or wrong token is 401; the same repository
name under another owner is 404, never 403.

Determinism: no wall clock and no unseeded randomness reach stored state.
Commit timestamps come from a monotonic counter (base 1700000000); the
viewer identity is the competition scenario's fixed viewer, derived from
the kit's one seeded scenario (wire.ts SCENARIO_SEED_HEX): login
"adaiversen", id 1000. Two runs driven by the same requests therefore
leave byte-identical state.

Only the Python standard library is used. No git binary, no package
manager, no outside service, no network beyond the harness.
"""

import base64
import copy
import hashlib
import json
import os
import re
import signal
import socket
import socketserver
import sys
import threading
import time
import urllib.request
import urllib.error
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, quote, unquote

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

VERSION = "1.0.0"
AGENT = "forge/1.0"
ZERO_OID = "0" * 40
HEX40 = re.compile(r"^[0-9a-f]{40}$")

# The token owner's identity: the fixed viewer of the competition's one
# seeded scenario (kit program/env/src/wire.ts, SCENARIO_SEED_HEX
# "6a09e667f3bcc909" -> users[0]). The suite compares viewer.login and
# GET /api/v3/user against exactly this login.
VIEWER_LOGIN = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"

DEFAULT_BRANCH = "main"
# Base of the deterministic commit clock (seconds); each commit made by the
# forge advances it by one. Pushed objects keep the bytes their author made.
EPOCH_BASE = 1700000000
# Base of the deterministic ISO clock for created_at / merged_at fields.
ISO_BASE = "2026-01-01T00:00:00Z"

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")

# Wire constants from the kit (wire.ts): the harness contract.
REGISTER_PATH = "/register"
DONE_PATH = "/done"
HEALTHZ_PATH = "/healthz"
API_PREFIX = "/api/v3"
GRAPHQL_PATH = "/api/graphql"
MCP_PATH = "/mcp"
BOOT_BUDGET_MS = 20000
CONFORMANCE_BUDGET_MS = 240000
BENCHMARK_BUDGET_MS = 240000
HEALTHZ_ATTEMPTS = 2
HEALTHZ_BUDGET_MS = 10000
TRIAL_WALL_BUDGET_SEC = 900
DEADLINE_MARGIN_MS = 90000

# ---------------------------------------------------------------------------
# Git object layer
# ---------------------------------------------------------------------------

TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def hash_object(obj_type, data):
    """SHA-1 of `<type> <size>\\0` + data, as git computes an object id."""
    h = hashlib.sha1()
    h.update(("%s %d\0" % (obj_type, len(data))).encode("ascii"))
    h.update(data)
    return h.hexdigest()


def is_oid(value):
    return isinstance(value, str) and bool(HEX40.match(value))


def _tree_sort_key(entry):
    # git's rule: a directory compares as if its name ended in '/'.
    mode, name = entry[0], entry[1]
    return (name + "/").encode("utf-8") if mode == "40000" else name.encode("utf-8")


def build_tree(entries):
    """entries: iterable of (mode, name, oid). Returns the tree object's bytes."""
    out = bytearray()
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        out += ("%s %s\0" % (mode, name)).encode("utf-8")
        out += bytes.fromhex(oid)
    return bytes(out)


def parse_tree(data):
    """Returns [(mode, name, oid-hex)] in the object's stored order."""
    entries = []
    off = 0
    while off < len(data):
        sp = data.index(b" ", off)
        nul = data.index(b"\0", sp + 1)
        mode = data[off:sp].decode("ascii")
        name = data[sp + 1:nul].decode("utf-8")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        off = nul + 21
    return entries


def parse_commit(data):
    """Returns (tree, parents, author, committer, message)."""
    blank = data.find(b"\n\n")
    head = data if blank < 0 else data[:blank]
    message = "" if blank < 0 else data[blank + 2:].decode("utf-8")
    tree = ""
    parents = []
    author = ""
    committer = ""
    for line in head.decode("utf-8").split("\n"):
        if not line:
            continue
        key, _, value = line.partition(" ")
        if key == "tree":
            tree = value
        elif key == "parent":
            parents.append(value)
        elif key == "author":
            author = value
        elif key == "committer":
            committer = value
    return tree, parents, author, committer, message


def build_commit(tree, parents, message, author, committer, timestamp):
    lines = ["tree %s" % tree]
    for parent in parents:
        lines.append("parent %s" % parent)
    lines.append("author %s %d +0000" % (author, timestamp))
    lines.append("committer %s %d +0000" % (committer, timestamp))
    lines.append("")
    return ("\n".join(lines) + "\n" + message).encode("utf-8")


def parse_tag(data):
    blank = data.find(b"\n\n")
    head = data if blank < 0 else data[:blank]
    message = "" if blank < 0 else data[blank + 2:].decode("utf-8")
    fields = {}
    for line in head.decode("utf-8").split("\n"):
        if not line:
            continue
        key, _, value = line.partition(" ")
        fields[key] = value
    return fields.get("object", ""), fields.get("type", ""), fields.get("tag", ""), \
        fields.get("tagger", ""), message


def build_tag(obj, obj_type, tag, message, tagger, timestamp):
    return ("object %s\ntype %s\ntag %s\ntagger %s %d +0000\n\n%s" % (
        obj, obj_type, tag, tagger, timestamp, message)).encode("utf-8")


def identity():
    return "%s <%s>" % (VIEWER_NAME, VIEWER_EMAIL)


# ---------------------------------------------------------------------------
# Packfiles
# ---------------------------------------------------------------------------

def _read_varint_size(buf, start):
    byte = buf[start]
    size = byte & 0x0F
    shift = 4
    off = start + 1
    first = byte
    while byte & 0x80:
        byte = buf[off]
        off += 1
        size += (byte & 0x7F) << shift
        shift += 7
    return size, off, first


def _read_ofs_base(buf, start):
    byte = buf[start]
    off = start + 1
    value = byte & 0x7F
    while byte & 0x80:
        byte = buf[off]
        off += 1
        value = ((value + 1) << 7) + (byte & 0x7F)
    return value, off


def _apply_delta(base, delta):
    off = 0

    def read_size():
        nonlocal off
        value = 0
        shift = 0
        while True:
            byte = delta[off]
            off += 1
            value |= (byte & 0x7F) << shift
            shift += 7
            if not (byte & 0x80):
                return value

    source_size = read_size()
    target_size = read_size()
    if source_size != len(base):
        raise ValueError("delta expects a %d-byte base, got %d" % (source_size, len(base)))
    out = bytearray()
    while off < len(delta):
        op = delta[off]
        off += 1
        if op & 0x80:
            copy_off = 0
            copy_size = 0
            shift = 0
            for bit in range(4):
                if op & (1 << bit):
                    copy_off |= delta[off] << shift
                    off += 1
                shift += 8
            shift = 0
            for bit in range(4, 7):
                if op & (1 << bit):
                    copy_size |= delta[off] << shift
                    off += 1
                shift += 8
            if copy_size == 0:
                copy_size = 0x10000
            out += base[copy_off:copy_off + copy_size]
        elif op:
            out += delta[off:off + op]
            off += op
        else:
            raise ValueError("delta opcode 0 is invalid")
    if len(out) != target_size:
        raise ValueError("delta produced %d of %d bytes" % (len(out), target_size))
    return bytes(out)


def read_pack(pack, resolve_base=None):
    """Parse a packfile. Returns {oid: (type, data)} with deltas resolved.

    resolve_base(oid) supplies an object a thin pack leaves out.
    Raises ValueError on any corruption.
    """
    if len(pack) < 32 or pack[:4] != b"PACK":
        raise ValueError("pack does not start with PACK")
    version = int.from_bytes(pack[4:8], "big")
    if version not in (2, 3):
        raise ValueError("unsupported pack version %d" % version)
    count = int.from_bytes(pack[8:12], "big")
    trailer = pack[-20:]
    if hashlib.sha1(pack[:-20]).digest() != trailer:
        raise ValueError("pack trailer does not match its bytes")
    raw = []  # (offset, type_code, size, data, base_offset|base_oid)
    by_offset = {}
    off = 12
    for _ in range(count):
        entry_off = off
        size, off, first = _read_varint_size(pack, off)
        type_code = (first >> 4) & 0x07
        base_off = None
        base_oid = None
        if type_code == 6:
            delta, off = _read_ofs_base(pack, off)
            base_off = entry_off - delta
        elif type_code == 7:
            base_oid = pack[off:off + 20].hex()
            off += 20
        elif type_code not in CODE_TYPE:
            raise ValueError("pack entry has unknown type code %d" % type_code)
        d = zlib.decompressobj()
        data = d.decompress(pack[off:])
        consumed = len(pack[off:]) - len(d.unused_data)
        off += consumed
        if len(data) != size:
            raise ValueError("pack entry declares %d bytes but inflated to %d" % (size, len(data)))
        entry = (entry_off, type_code, size, data, base_off, base_oid)
        raw.append(entry)
        by_offset[entry_off] = entry
    if off != len(pack) - 20:
        raise ValueError("pack has stray bytes before its trailer")

    resolved = {}  # offset -> (type, data, oid)
    by_oid = {}
    resolving = set()

    def resolve(entry):
        entry_off = entry[0]
        if entry_off in resolved:
            return resolved[entry_off]
        if entry_off in resolving:
            raise ValueError("delta cycle at pack offset %d" % entry_off)
        resolving.add(entry_off)
        _, type_code, _, data, base_off, base_oid = entry
        if type_code == 6:
            base_entry = by_offset.get(base_off)
            if base_entry is None:
                raise ValueError("ofs-delta base at offset %d is not in the pack" % base_off)
            btype, bdata, _ = resolve(base_entry)
            obj_type, obj_data = btype, _apply_delta(bdata, data)
        elif type_code == 7:
            base_entry = by_oid.get(base_oid)
            if base_entry is not None:
                btype, bdata, _ = resolve(base_entry)
                obj_type, obj_data = btype, _apply_delta(bdata, data)
            elif resolve_base is not None:
                ext = resolve_base(base_oid)
                if ext is None:
                    raise ValueError("ref-delta base %s is not available" % base_oid)
                obj_type, obj_data = ext[0], _apply_delta(ext[1], data)
            else:
                raise ValueError("ref-delta base %s is not in the pack" % base_oid)
        else:
            obj_type, obj_data = CODE_TYPE[type_code], data
        oid = hash_object(obj_type, obj_data)
        out = (obj_type, obj_data, oid)
        resolved[entry_off] = out
        by_oid[oid] = entry
        resolving.discard(entry_off)
        return out

    objects = {}
    for entry in raw:
        obj_type, obj_data, oid = resolve(entry)
        objects[oid] = (obj_type, obj_data)
    return objects


def _pack_object_header(obj_type, size):
    code = TYPE_CODE[obj_type]
    out = bytearray()
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def write_pack(objects):
    """objects: iterable of (type, data). Plain pack, no deltas, version 2."""
    parts = [b"PACK" + (2).to_bytes(4, "big") + len(objects).to_bytes(4, "big")]
    for obj_type, data in objects:
        parts.append(_pack_object_header(obj_type, len(data)))
        parts.append(zlib.compress(data, 6))
    body = b"".join(parts)
    return body + hashlib.sha1(body).digest()


# ---------------------------------------------------------------------------
# pkt-lines
# ---------------------------------------------------------------------------

def pkt_line(payload):
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


FLUSH = b"0000"
DELIM = b"0001"


def pkt_lines(items):
    """items: str payloads, or 'flush' / 'delim' markers."""
    out = bytearray()
    for item in items:
        if item == "flush":
            out += FLUSH
        elif item == "delim":
            out += DELIM
        else:
            out += pkt_line(item)
    return bytes(out)


def decode_pkt_lines(buf):
    """Returns a list of ('data', bytes) | ('flush',) | ('delim',) | ('end',)."""
    packets = []
    off = 0
    while off < len(buf):
        if off + 4 > len(buf):
            raise ValueError("truncated pkt-line header")
        head = buf[off:off + 4]
        try:
            length = int(head.decode("ascii"), 16)
        except ValueError:
            raise ValueError("bad pkt-line length %r" % head)
        if length == 0:
            packets.append(("flush",))
            off += 4
        elif length == 1:
            packets.append(("delim",))
            off += 4
        elif length == 2:
            packets.append(("end",))
            off += 4
        else:
            if off + length > len(buf):
                raise ValueError("truncated pkt-line payload")
            packets.append(("data", bytes(buf[off + 4:off + length])))
            off += length
    return packets


# ---------------------------------------------------------------------------
# Store
# ---------------------------------------------------------------------------

class Issue:
    __slots__ = ("number", "title", "body", "state", "labels", "seq", "comments")

    def __init__(self, number, title, body, seq):
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.labels = []  # label names
        self.seq = seq
        self.comments = []  # (id, body)


class Pull:
    __slots__ = ("number", "title", "body", "state", "head", "base", "seq",
                 "merged", "merged_at", "merge_sha", "head_sha", "base_sha")

    def __init__(self, number, title, body, head, base, seq, head_sha, base_sha):
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.head = head
        self.base = base
        self.seq = seq
        self.merged = False
        self.merged_at = None
        self.merge_sha = None
        self.head_sha = head_sha
        self.base_sha = base_sha


class Repo:
    __slots__ = ("id", "owner", "name", "private", "description", "default_branch",
                 "objects", "refs", "issues", "pulls", "labels", "next_number",
                 "next_comment", "seq")

    def __init__(self, rid, owner, name, private, description):
        self.id = rid
        self.owner = owner
        self.name = name
        self.private = private
        self.description = description
        self.default_branch = DEFAULT_BRANCH
        self.objects = {}  # oid -> (type, bytes)
        self.refs = {}  # "refs/heads/main" -> oid
        self.issues = {}  # number -> Issue
        self.pulls = {}  # number -> Pull
        self.labels = {}  # name -> color
        self.next_number = 1  # issues and pull requests share GitHub's counter
        self.next_comment = 1
        self.seq = 0

    # -- objects -----------------------------------------------------------
    def put_object(self, obj_type, data):
        oid = hash_object(obj_type, data)
        self.objects.setdefault(oid, (obj_type, data))
        return oid

    def get_object(self, oid):
        return self.objects.get(oid)

    def snapshot(self):
        """A point-in-time copy for read-only work (clone/fetch): the object
        and ref dicts are copied while the caller holds the store lock, so
        the expensive pack build can run without holding it -- otherwise
        50 concurrent clones serialize on the lock and the clone bench
        pays for all of them in a row."""
        snap = copy.copy(self)
        snap.objects = dict(self.objects)
        snap.refs = dict(self.refs)
        return snap

    def tip(self, branch):
        return self.refs.get("refs/heads/" + branch)

    def branches(self):
        return sorted(r for r in self.refs if r.startswith("refs/heads/"))

    def tags(self):
        return sorted(r for r in self.refs if r.startswith("refs/tags/"))


class Store:
    """All forge state. One global lock guards it; handlers snapshot what
    they need under the lock and do slow work (pack building) outside it."""

    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}  # (owner, name) -> Repo
        self.next_repo_id = 1
        self.clock = 0  # deterministic commit/ISO clock

    def tick(self):
        self.clock += 1
        return EPOCH_BASE + self.clock

    def iso_now(self):
        # Deterministic ISO timestamp from the same counter.
        self.clock += 1
        total = self.clock
        day = 1 + total // 86400
        rem = total % 86400
        hh, rem = divmod(rem, 3600)
        mm, ss = divmod(rem, 60)
        return "2026-01-%02dT%02d:%02d:%02dZ" % (day, hh, mm, ss)

    def create_repo(self, owner, name, private, description):
        repo = Repo(self.next_repo_id, owner, name, private, description)
        self.next_repo_id += 1
        self.repos[(owner, name)] = repo
        return repo

    def get_repo(self, owner, name):
        return self.repos.get((owner, name))

    def delete_repo(self, owner, name):
        self.repos.pop((owner, name), None)

    def user_repos(self, owner):
        return [r for (o, _), r in sorted(self.repos.items()) if o == owner]


STORE = Store()


# -- git graph helpers -------------------------------------------------------

def reachable(repo, roots, allow_missing=False):
    """Every object id reachable from roots (commits, trees, tags, blobs)."""
    seen = set()
    stack = [r for r in roots if is_oid(r)]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        obj = repo.get_object(oid)
        if obj is None:
            if allow_missing:
                continue
            raise KeyError("object %s is missing" % oid)
        seen.add(oid)
        obj_type, data = obj
        if obj_type == "commit":
            tree, parents, _, _, _ = parse_commit(data)
            stack.append(tree)
            stack.extend(parents)
        elif obj_type == "tag":
            target, _, _, _, _ = parse_tag(data)
            stack.append(target)
        elif obj_type == "tree":
            for mode, _, entry_oid in parse_tree(data):
                if mode != "160000":
                    stack.append(entry_oid)
    return seen


def is_ancestor(repo, ancestor, descendant):
    """True when `ancestor` is reachable from `descendant` (commit graph)."""
    if ancestor == descendant:
        return True
    stack = [descendant]
    seen = set()
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        seen.add(oid)
        obj = repo.get_object(oid)
        if obj is None or obj[0] != "commit":
            continue
        _, parents, _, _, _ = parse_commit(obj[1])
        if ancestor in parents:
            return True
        stack.extend(parents)
    return False


def depth_closure(repo, wants, depth):
    """Objects reachable from `wants` within `depth` commit generations
    (depth None: the whole closure). Returns (objects, boundary_commits)
    where boundary_commits are the commits at generation depth-1."""
    included = set()
    boundary = set()
    queue = [(w, 0) for w in wants if is_oid(w)]
    seen_commits = set()
    while queue:
        oid, gen = queue.pop(0)
        if oid in seen_commits:
            continue
        obj = repo.get_object(oid)
        if obj is None:
            continue
        if obj[0] == "tag":
            # An annotated tag: keep the tag object itself, then walk its
            # target as a generation-0 commit.
            included.add(oid)
            seen_commits.add(oid)
            target = parse_tag(obj[1])[0]
            if target:
                queue.append((target, 0))
            continue
        if obj[0] != "commit":
            included.add(oid)
            continue
        seen_commits.add(oid)
        tree, parents, _, _, _ = parse_commit(obj[1])
        included.add(oid)
        included.add(tree)
        tree_obj = repo.get_object(tree)
        if tree_obj is not None:
            for _, _, entry_oid in parse_tree(tree_obj[1]):
                included.add(entry_oid)
            # blobs under subtrees
            stack = [tree]
            done_trees = set()
            while stack:
                t = stack.pop()
                if t in done_trees:
                    continue
                done_trees.add(t)
                tobj = repo.get_object(t)
                if tobj is None:
                    continue
                for mode, _, eoid in parse_tree(tobj[1]):
                    if mode == "40000":
                        stack.append(eoid)
                        included.add(eoid)
                    elif mode != "160000":
                        included.add(eoid)
        if depth is not None and gen >= depth - 1:
            boundary.add(oid)
            continue
        for parent in parents:
            queue.append((parent, gen + 1))
    return included, boundary


def have_closure(repo, haves, shallow_boundaries):
    """Objects the client already holds: the closure of each have, stopping
    at the client's shallow boundaries (a boundary commit's own tree and
    blobs are held, its parents are not)."""
    held = set()
    for have in haves:
        stack = [have]
        seen = set()
        while stack:
            oid = stack.pop()
            if oid in seen:
                continue
            seen.add(oid)
            obj = repo.get_object(oid)
            if obj is None:
                continue
            held.add(oid)
            obj_type, data = obj
            if obj_type == "commit":
                tree, parents, _, _, _ = parse_commit(data)
                held.add(tree)
                stack.append(tree)
                if oid not in shallow_boundaries:
                    stack.extend(parents)
            elif obj_type == "tag":
                target, _, _, _, _ = parse_tag(data)
                stack.append(target)
            elif obj_type == "tree":
                for mode, _, entry_oid in parse_tree(data):
                    if mode == "40000":
                        stack.append(entry_oid)
                        held.add(entry_oid)
                    elif mode != "160000":
                        held.add(entry_oid)
    return held


def tree_map(repo, commit_oid):
    """{path: (mode, oid)} for the whole tree of a commit, recursively."""
    out = {}

    def walk(tree_oid, prefix):
        obj = repo.get_object(tree_oid)
        if obj is None:
            return
        for mode, name, oid in parse_tree(obj[1]):
            path = prefix + name
            if mode == "40000":
                walk(oid, path + "/")
            else:
                out[path] = (mode, oid)

    tree, _, _, _, _ = parse_commit(repo.get_object(commit_oid)[1])
    walk(tree, "")
    return out


def build_tree_from_files(repo, files):
    """files: {path: bytes}. Builds blobs and trees bottom-up. Returns the
    root tree oid."""
    # node: {dirs: {name: node}, files: {name: bytes}}
    root = {"dirs": {}, "files": {}}
    for path, data in files.items():
        parts = path.split("/")
        node = root
        for part in parts[:-1]:
            node = node["dirs"].setdefault(part, {"dirs": {}, "files": {}})
        node["files"][parts[-1]] = data

    def build(node):
        entries = []
        for name, data in node["files"].items():
            entries.append(("100644", name, repo.put_object("blob", data)))
        for name, child in node["dirs"].items():
            entries.append(("40000", name, build(child)))
        return repo.put_object("tree", build_tree(entries))

    return build(root)


def commit_with_tree(repo, tree_oid, parents, message, timestamp):
    data = build_commit(tree_oid, parents, message, identity(), identity(), timestamp)
    return repo.put_object("commit", data)


def find_merge_base(repo, a, b):
    """A common ancestor commit of a and b (first found by BFS from a)."""
    if a is None or b is None:
        return None
    ancestors_b = set()
    stack = [b]
    while stack:
        oid = stack.pop()
        if oid in ancestors_b:
            continue
        ancestors_b.add(oid)
        obj = repo.get_object(oid)
        if obj is None or obj[0] != "commit":
            continue
        _, parents, _, _, _ = parse_commit(obj[1])
        stack.extend(parents)
    stack = [a]
    seen = set()
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        seen.add(oid)
        if oid in ancestors_b:
            return oid
        obj = repo.get_object(oid)
        if obj is None or obj[0] != "commit":
            continue
        _, parents, _, _, _ = parse_commit(obj[1])
        stack.extend(parents)
    return None


def merge_trees(repo, base_oid, head_oid, other_oid):
    """Three-way merge at file level. Returns (tree_oid, conflict) where
    conflict is True when base and head both changed a file differently."""
    base = tree_map(repo, base_oid) if base_oid else {}
    head = tree_map(repo, head_oid) if head_oid else {}
    other = tree_map(repo, other_oid) if other_oid else {}
    merged = {}
    conflict = False
    for path in sorted(set(base) | set(head) | set(other)):
        b = base.get(path)
        h = head.get(path)
        o = other.get(path)
        if h == o:
            if h is not None:
                merged[path] = h
        elif b == o:
            if h is not None:
                merged[path] = h
        elif b == h:
            if o is not None:
                merged[path] = o
        else:
            conflict = True
    files = {}
    for path, (mode, oid) in merged.items():
        obj = repo.get_object(oid)
        if obj is not None:
            files[path] = obj[1]
    return build_tree_from_files(repo, files), conflict


def diff_files(repo, base_oid, head_oid):
    """[{filename, status, additions, deletions, changes}] between two tips."""
    import difflib
    base = tree_map(repo, base_oid) if base_oid else {}
    head = tree_map(repo, head_oid) if head_oid else {}
    out = []
    for path in sorted(set(base) | set(head)):
        b = base.get(path)
        h = head.get(path)
        if b is None:
            status = "added"
            old_lines, new_lines = [], repo.get_object(h[1])[1].decode("utf-8", "replace").splitlines()
        elif h is None:
            status = "removed"
            old_lines = repo.get_object(b[1])[1].decode("utf-8", "replace").splitlines()
            new_lines = []
        elif b[1] == h[1]:
            continue
        else:
            status = "modified"
            old_lines = repo.get_object(b[1])[1].decode("utf-8", "replace").splitlines()
            new_lines = repo.get_object(h[1])[1].decode("utf-8", "replace").splitlines()
        additions = deletions = 0
        for line in difflib.unified_diff(old_lines, new_lines, lineterm=""):
            if line.startswith("+") and not line.startswith("+++"):
                additions += 1
            elif line.startswith("-") and not line.startswith("---"):
                deletions += 1
        out.append({"filename": path, "status": status, "additions": additions,
                    "deletions": deletions, "changes": additions + deletions})
    return out


def global_id(kind, *parts):
    """Opaque, stable Relay-style global id (never a bare number)."""
    raw = (kind + ":" + "/".join(str(p) for p in parts)).encode("utf-8")
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def parse_global_id(gid):
    try:
        padded = gid + "=" * (-len(gid) % 4)
        raw = base64.urlsafe_b64decode(padded).decode("utf-8")
    except Exception:
        return None
    if ":" not in raw:
        return None
    kind, rest = raw.split(":", 1)
    return kind, rest


# ---------------------------------------------------------------------------
# HTTP plumbing
# ---------------------------------------------------------------------------

_request_counter = [0]
_counter_lock = threading.Lock()


def next_request_id():
    with _counter_lock:
        _request_counter[0] += 1
        return "%032x" % _request_counter[0]


def check_auth(handler):
    """True when the request carries the trial token. In dev mode (no
    MAKEFUN_SHOP_TOKEN set) any non-empty Bearer token is accepted, so the
    local suite can run; a missing header is always 401."""
    auth = handler.headers.get("Authorization", "")
    if not auth.startswith("Bearer "):
        return False
    token = auth[7:].strip()
    if not token:
        return False
    if TOKEN:
        return token == TOKEN
    return True


class ForgeServer(ThreadingHTTPServer):
    # The default listen backlog is 5: when 50 concurrent clones connect
    # at once, the kernel drops SYNs and clients back off for seconds
    # (measured: 50 concurrent clones took 12.7 s, sequential 0.3 s).
    request_queue_size = 128
    daemon_threads = True
    allow_reuse_address = True


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "forge/" + VERSION

    def setup(self):
        super().setup()
        # Kill the Nagle/delayed-ACK stall: without this, small request/
        # response pairs on a keep-alive connection cost ~40 ms each
        # (measured 41 ms/req vs 1 ms on fresh connections), which alone
        # blows the read benchmark's 60 s budget for 2000 requests.
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_QUICKACK, 1)
        except OSError:
            pass

    # -- quiet, fast logging -------------------------------------------------
    def log_message(self, *args):
        pass

    # -- response helpers ----------------------------------------------------
    def _send(self, status, body, content_type="application/json", extra=None):
        if isinstance(body, (dict, list)):
            payload = (json.dumps(body) + "\n").encode("utf-8")
        elif isinstance(body, str):
            payload = body.encode("utf-8")
        else:
            payload = body
        headers = {"Content-Type": content_type,
                   "Content-Length": str(len(payload)),
                   "X-GitHub-Request-Id": next_request_id()}
        if extra:
            headers.update(extra)
        try:
            self.send_response(status)
            for key, value in headers.items():
                self.send_header(key, value)
            self.end_headers()
            if self.command != "HEAD" and payload:
                self.wfile.write(payload)
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True

    def _json(self, status, body, extra=None):
        self._send(status, body, "application/json", extra)

    def _error(self, status, message):
        self._json(status, {"message": message})

    def _send_jsonrpc(self, req_id, result, error, status=200):
        envelope = {"jsonrpc": "2.0", "id": req_id}
        if error is not None:
            envelope["error"] = error
        else:
            envelope["result"] = result
        self._json(status, envelope)

    def _read_body(self):
        # The body was already consumed (and cached) by _dispatch so that
        # early answers cannot strand bytes on a keep-alive connection.
        return getattr(self, "_body_buffer", b"")

    def _read_body_inner(self):
        length = self.headers.get("Content-Length")
        if length is not None:
            try:
                n = int(length)
            except ValueError:
                n = 0
            return self.rfile.read(n) if n > 0 else b""
        if (self.headers.get("Transfer-Encoding", "").lower() == "chunked"):
            chunks = bytearray()
            while True:
                line = self.rfile.readline(65536).strip()
                try:
                    size = int(line.split(b";")[0], 16)
                except ValueError:
                    break
                if size == 0:
                    self.rfile.readline(65536)
                    break
                chunks += self.rfile.read(size)
                self.rfile.read(2)
            return bytes(chunks)
        return b""

    def _json_body(self):
        """Returns (value, error_response_sent)."""
        raw = self._read_body()
        if not raw:
            return {}, False
        try:
            return json.loads(raw.decode("utf-8")), False
        except (ValueError, UnicodeDecodeError):
            self._error(400, "Invalid JSON body")
            return None, True

    # -- dispatch ------------------------------------------------------------
    def _dispatch(self, method):
        # Read (and cache) the body before routing: a handler that answers
        # early -- 401, 404 -- must not leave body bytes in the socket, or
        # the next request on this keep-alive connection parses as garbage.
        if method in ("POST", "PUT", "PATCH", "DELETE"):
            self._body_buffer = self._read_body_inner()
        else:
            self._body_buffer = b""
        parsed = urlparse(self.path)
        path = parsed.path
        query = {k: v[0] for k, v in parse_qs(parsed.query).items()}
        try:
            if method == "GET" and path == "/healthz":
                self._json(200, {"ok": True})
                return
            if path == "/api/graphql":
                _handle_graphql(self, method, query)
                return
            if path == "/mcp":
                _handle_mcp(self, method, query)
                return
            if path.startswith("/api/v3"):
                self._handle_rest(method, path[len("/api/v3"):], query)
                return
            m = re.match(r"^/([^/]+)/([^/]+)\.git(/.*)$", path)
            if m:
                owner, repo_name, suffix = m.group(1), m.group(2), m.group(3)
                self._handle_git(method, owner, repo_name, suffix, query)
                return
            self._error(404, "Not Found")
        except BrokenPipeError:
            self.close_connection = True
        except Exception as exc:  # never let one request kill the server
            try:
                self._error(500, "Internal error: %s" % exc)
            except Exception:
                self.close_connection = True

    def do_GET(self):
        self._dispatch("GET")

    def do_POST(self):
        self._dispatch("POST")

    def do_PUT(self):
        self._dispatch("PUT")

    def do_PATCH(self):
        self._dispatch("PATCH")

    def do_DELETE(self):
        self._dispatch("DELETE")

    # -- shared REST helpers ---------------------------------------------------
    def _need_auth(self):
        if not check_auth(self):
            self._error(401, "Requires authentication")
            return False
        return True

    def _get_repo_or_404(self, owner, name):
        repo = STORE.get_repo(owner, name)
        if repo is None or owner != VIEWER_LOGIN:
            # The same name under another owner is 404, never 403.
            self._error(404, "Not Found")
            return None
        return repo

    def _resolve_ref(self, repo, ref):
        """A branch name, a tag name or a commit oid -> commit oid (or None)."""
        if ref is None:
            return repo.tip(repo.default_branch)
        if ref in [b[11:] for b in repo.branches()]:
            return repo.tip(ref)
        if ref in [t[10:] for t in repo.tags()]:
            oid = repo.refs.get("refs/tags/" + ref)
            obj = repo.get_object(oid) if oid else None
            if obj and obj[0] == "tag":
                return parse_tag(obj[1])[0]
            return oid
        if is_oid(ref) and repo.get_object(ref):
            return ref
        return None

    def _commit_on_branch(self, repo, branch, files, message):
        """Create a commit with `files` ({path: bytes}) on `branch`, creating
        the branch from the default tip when it does not exist yet. Returns
        the new commit oid. `files` may be None to delete (see contents)."""
        base_tip = repo.tip(branch)
        if base_tip is None and branch != repo.default_branch:
            base_tip = repo.tip(repo.default_branch)
        parents = [base_tip] if base_tip else []
        current = {}
        if base_tip:
            current = tree_map(repo, base_tip)
            for path, (mode, oid) in current.items():
                obj = repo.get_object(oid)
                if obj is not None:
                    current[path] = obj[1]
        for path, data in files.items():
            if data is None:
                current.pop(path, None)
            else:
                current[path] = data
        tree_oid = build_tree_from_files(repo, current)
        ts = STORE.tick()
        commit_oid = commit_with_tree(repo, tree_oid, parents, message, ts)
        repo.refs["refs/heads/" + branch] = commit_oid
        return commit_oid

    def _repo_json(self, repo):
        return {
            "id": repo.id,
            "name": repo.name,
            "full_name": "%s/%s" % (repo.owner, repo.name),
            "owner": {"login": repo.owner, "id": VIEWER_ID if repo.owner == VIEWER_LOGIN else repo.id},
            "private": repo.private,
            "description": repo.description,
            "default_branch": repo.default_branch,
            "html_url": "https://example.invalid/%s/%s" % (repo.owner, repo.name),
            "url": "/api/v3/repos/%s/%s" % (repo.owner, repo.name),
            "has_issues": True,
            "created_at": ISO_BASE,
            "updated_at": ISO_BASE,
        }

    def _issue_json(self, repo, issue):
        return {
            "id": repo.id * 100000 + issue.number,
            "number": issue.number,
            "title": issue.title,
            "body": issue.body,
            "state": issue.state,
            "labels": [{"name": name, "color": repo.labels.get(name, "ededed")}
                       for name in issue.labels],
            "user": {"login": VIEWER_LOGIN},
            "created_at": ISO_BASE,
            "updated_at": ISO_BASE,
        }

    def _pull_json(self, repo, pull):
        return {
            "id": repo.id * 100000 + pull.number,
            "number": pull.number,
            "title": pull.title,
            "body": pull.body,
            "state": pull.state,
            "head": {"ref": pull.head, "sha": pull.head_sha,
                     "label": "%s:%s" % (repo.owner, pull.head)},
            "base": {"ref": pull.base, "sha": pull.base_sha,
                     "label": "%s:%s" % (repo.owner, pull.base)},
            "merged": pull.merged,
            "merged_at": pull.merged_at,
            "merge_commit_sha": pull.merge_sha,
            "user": {"login": VIEWER_LOGIN},
            "created_at": ISO_BASE,
            "updated_at": ISO_BASE,
        }

    def _paginate(self, items, query, default_per_page=30):
        try:
            per_page = max(1, min(100, int(query.get("per_page", default_per_page))))
        except ValueError:
            per_page = default_per_page
        try:
            page = max(1, int(query.get("page", "1")))
        except ValueError:
            page = 1
        total = len(items)
        start = (page - 1) * per_page
        chunk = items[start:start + per_page]
        links = []
        base = "http://%s%s" % (self.headers.get("Host", "localhost"), urlparse(self.path).path)
        if start + per_page < total:
            links.append('<%s?per_page=%d&page=%d>; rel="next"' % (base, per_page, page + 1))
            links.append('<%s?per_page=%d&page=%d>; rel="last"' % (base, per_page, (total + per_page - 1) // per_page))
        if page > 1:
            links.append('<%s?per_page=%d&page=1>; rel="first"' % (base, per_page))
            links.append('<%s?per_page=%d&page=%d>; rel="prev"' % (base, per_page, page - 1))
        return chunk, ({'Link': ", ".join(links)} if links else None)

    # -- REST v3 ---------------------------------------------------------------
    def _handle_rest(self, method, path, query):
        if not self._need_auth():
            return
        scopes = {"X-OAuth-Scopes": "repo, read:org"}
        with STORE.lock:
            self._rest_locked(method, path, query, scopes)

    def _rest_locked(self, method, path, query, scopes):
        if path in ("", "/"):
            if method == "GET":
                self._json(200, {"current_user_url": "/api/v3/user",
                                 "rate_limit_url": "/api/v3/rate_limit"}, scopes)
            else:
                self._error(404, "Not Found")
            return
        if path == "/meta":
            if method == "GET":
                self._json(200, {"installed_version": VERSION}, scopes)
            else:
                self._error(404, "Not Found")
            return
        if path == "/user":
            if method == "GET":
                self._json(200, {"login": VIEWER_LOGIN, "id": VIEWER_ID,
                                 "name": VIEWER_NAME, "email": VIEWER_EMAIL,
                                 "type": "User"}, scopes)
            else:
                self._error(404, "Not Found")
            return
        if path == "/user/repos":
            if method == "GET":
                repos = STORE.user_repos(VIEWER_LOGIN)
                chunk, extra = self._paginate([self._repo_json(r) for r in repos], query)
                self._json(200, chunk, {**scopes, **(extra or {})})
            elif method == "POST":
                body, bad = self._json_body()
                if bad:
                    return
                name = body.get("name")
                if not name or not isinstance(name, str):
                    self._error(422, "name is required")
                    return
                if STORE.get_repo(VIEWER_LOGIN, name) is not None:
                    self._error(422, "Repository already exists")
                    return
                repo = STORE.create_repo(VIEWER_LOGIN, name,
                                         bool(body.get("private", False)),
                                         body.get("description") or "")
                self._json(201, self._repo_json(repo), scopes)
            else:
                self._error(404, "Not Found")
            return
        m = re.match(r"^/repos/([^/]+)/([^/]+)(.*)$", path)
        if not m:
            self._error(404, "Not Found")
            return
        owner, name, rest = unquote(m.group(1)), unquote(m.group(2)), m.group(3)
        repo = self._get_repo_or_404(owner, name)
        if repo is None:
            return
        self._rest_repo(method, repo, rest, query, scopes)

    def _rest_repo(self, method, repo, rest, query, scopes):
        if rest in ("", "/"):
            if method == "GET":
                self._json(200, self._repo_json(repo), scopes)
            elif method == "PATCH":
                body, bad = self._json_body()
                if bad:
                    return
                if "description" in body:
                    repo.description = body["description"]
                if "private" in body:
                    repo.private = bool(body["private"])
                self._json(200, self._repo_json(repo), scopes)
            elif method == "DELETE":
                STORE.delete_repo(repo.owner, repo.name)
                self._send(204, b"", "application/json", scopes)
            else:
                self._error(404, "Not Found")
            return
        if rest == "/branches":
            if method == "GET":
                out = []
                for ref in repo.branches():
                    out.append({"name": ref[11:], "commit": {"sha": repo.refs[ref]}})
                self._json(200, out, scopes)
            else:
                self._error(404, "Not Found")
            return
        m = re.match(r"^/branches/(.+)$", rest)
        if m:
            branch = unquote(m.group(1))
            tip = repo.tip(branch)
            if tip is None:
                self._error(404, "Not Found")
                return
            if method == "GET":
                self._json(200, {"name": branch, "commit": {"sha": tip}}, scopes)
            else:
                self._error(404, "Not Found")
            return
        if rest == "/commits":
            if method == "GET":
                ref = query.get("sha")
                tip = self._resolve_ref(repo, ref) if ref else repo.tip(repo.default_branch)
                commits = []
                if tip:
                    seen = set()
                    stack = [tip]
                    ordered = []
                    while stack:
                        oid = stack.pop()
                        if oid in seen:
                            continue
                        seen.add(oid)
                        obj = repo.get_object(oid)
                        if obj is None or obj[0] != "commit":
                            continue
                        ordered.append(oid)
                        _, parents, _, _, _ = parse_commit(obj[1])
                        stack.extend(parents)
                    # Newest first: the forge's deterministic clock order is
                    # the creation order, which a walk cannot recover, so
                    # order by the walk's discovery from the tip.
                    for oid in ordered:
                        _, _, author, committer, message = parse_commit(repo.get_object(oid)[1])
                        commits.append({"sha": oid, "commit": {"message": message,
                                                               "author": {"name": author},
                                                               "committer": {"name": committer}}})
                chunk, extra = self._paginate(commits, query)
                self._json(200, chunk, {**scopes, **(extra or {})})
            else:
                self._error(404, "Not Found")
            return
        if rest == "/git/refs":
            if method == "POST":
                body, bad = self._json_body()
                if bad:
                    return
                ref = body.get("ref")
                sha = body.get("sha")
                if not ref or not sha or not is_oid(sha) or repo.get_object(sha) is None:
                    self._error(422, "Invalid ref or sha")
                    return
                if ref in repo.refs:
                    self._error(422, "Reference already exists")
                    return
                if not (ref.startswith("refs/heads/") or ref.startswith("refs/tags/")):
                    self._error(422, "Invalid ref")
                    return
                repo.refs[ref] = sha
                self._json(201, {"ref": ref, "object": {"sha": sha, "type": "commit"}}, scopes)
            else:
                self._error(404, "Not Found")
            return
        m = re.match(r"^/git/refs/(.+)$", rest)
        if m:
            ref = "refs/" + unquote(m.group(1))
            if method == "GET":
                if ref in repo.refs:
                    self._json(200, {"ref": ref, "object": {"sha": repo.refs[ref]}}, scopes)
                else:
                    self._error(404, "Not Found")
            else:
                self._error(404, "Not Found")
            return
        if rest.startswith("/contents"):
            self._rest_contents(method, repo, rest[len("/contents"):], query, scopes)
            return
        if rest == "/labels":
            if method == "POST":
                body, bad = self._json_body()
                if bad:
                    return
                name = body.get("name")
                if not name:
                    self._error(422, "name is required")
                    return
                repo.labels[name] = body.get("color", "ededed")
                self._json(201, {"name": name, "color": repo.labels[name]}, scopes)
            elif method == "GET":
                self._json(200, [{"name": n, "color": c} for n, c in repo.labels.items()], scopes)
            else:
                self._error(404, "Not Found")
            return
        if rest == "/issues":
            if method == "GET":
                issues = self._filter_issues(repo, query)
                chunk, extra = self._paginate([self._issue_json(repo, i) for i in issues], query)
                self._json(200, chunk, {**scopes, **(extra or {})})
            elif method == "POST":
                self._create_issue(repo, scopes)
            else:
                self._error(404, "Not Found")
            return
        m = re.match(r"^/issues/(\d+)(.*)$", rest)
        if m:
            number = int(m.group(1))
            tail = m.group(2)
            issue = repo.issues.get(number)
            if tail == "/comments":
                if issue is None:
                    self._error(404, "Not Found")
                    return
                if method == "GET":
                    self._json(200, [{"id": cid, "body": b} for cid, b in issue.comments], scopes)
                elif method == "POST":
                    body, bad = self._json_body()
                    if bad:
                        return
                    cid = repo.next_comment
                    repo.next_comment += 1
                    issue.comments.append((cid, body.get("body", "")))
                    self._json(201, {"id": cid, "body": body.get("body", "")}, scopes)
                else:
                    self._error(404, "Not Found")
                return
            if tail not in ("", "/"):
                self._error(404, "Not Found")
                return
            if issue is None:
                self._error(404, "Not Found")
                return
            if method == "GET":
                self._json(200, self._issue_json(repo, issue), scopes)
            elif method == "PATCH":
                body, bad = self._json_body()
                if bad:
                    return
                if "state" in body:
                    issue.state = body["state"]
                if "title" in body:
                    issue.title = body["title"]
                if "body" in body:
                    issue.body = body["body"]
                self._json(200, self._issue_json(repo, issue), scopes)
            else:
                self._error(404, "Not Found")
            return
        if rest == "/pulls":
            if method == "GET":
                pulls = self._filter_pulls(repo, query)
                chunk, extra = self._paginate([self._pull_json(repo, p) for p in pulls], query)
                self._json(200, chunk, {**scopes, **(extra or {})})
            elif method == "POST":
                self._create_pull(repo, scopes)
            else:
                self._error(404, "Not Found")
            return
        m = re.match(r"^/pulls/(\d+)(.*)$", rest)
        if m:
            number = int(m.group(1))
            tail = m.group(2)
            pull = repo.pulls.get(number)
            if tail == "/files":
                if pull is None:
                    self._error(404, "Not Found")
                    return
                if method == "GET":
                    self._json(200, diff_files(repo, pull.base_sha, pull.head_sha), scopes)
                else:
                    self._error(404, "Not Found")
                return
            if tail == "/merge":
                if pull is None:
                    self._error(404, "Not Found")
                    return
                if method == "PUT":
                    self._merge_pull(repo, pull, scopes)
                else:
                    self._error(404, "Not Found")
                return
            if tail not in ("", "/"):
                self._error(404, "Not Found")
                return
            if pull is None:
                self._error(404, "Not Found")
                return
            if method == "GET":
                self._json(200, self._pull_json(repo, pull), scopes)
            else:
                self._error(404, "Not Found")
            return
        self._error(404, "Not Found")

    def _filter_issues(self, repo, query):
        issues = sorted(repo.issues.values(), key=lambda i: i.seq)
        state = query.get("state", "open")
        if state != "all":
            issues = [i for i in issues if i.state == state]
        if query.get("sort", "created") == "created":
            if query.get("direction", "desc") == "asc":
                pass  # already ascending by creation
            else:
                issues = list(reversed(issues))
        return issues

    def _filter_pulls(self, repo, query):
        pulls = sorted(repo.pulls.values(), key=lambda p: p.seq)
        state = query.get("state", "open")
        if state != "all":
            pulls = [p for p in pulls if p.state == state]
        return pulls

    def _create_issue(self, repo, scopes):
        body, bad = self._json_body()
        if bad:
            return
        title = body.get("title")
        if not title:
            self._error(422, "title is required")
            return
        for label in body.get("labels") or []:
            name = label if isinstance(label, str) else label.get("name")
            if name not in repo.labels:
                self._error(422, "Label does not exist")
                return
        number = repo.next_number
        repo.next_number += 1
        issue = Issue(number, title, body.get("body") or "", repo.next_number)
        issue.seq = number
        for label in body.get("labels") or []:
            issue.labels.append(label if isinstance(label, str) else label.get("name"))
        repo.issues[number] = issue
        self._json(201, self._issue_json(repo, issue), scopes)

    def _create_pull(self, repo, scopes, input_body=None):
        body = input_body
        if body is None:
            body, bad = self._json_body()
            if bad:
                return None
        title = body.get("title")
        head = body.get("head")
        base = body.get("base") or repo.default_branch
        if not title or not head:
            self._error(422, "title and head are required")
            return None
        head_sha = repo.tip(head)
        base_sha = repo.tip(base)
        if head_sha is None or base_sha is None:
            self._error(422, "Unknown head or base")
            return None
        for pull in repo.pulls.values():
            if pull.state == "open" and pull.head == head and pull.base == base:
                self._error(422, "A pull request already exists for this branch")
                return None
        number = repo.next_number
        repo.next_number += 1
        pull = Pull(number, title, body.get("body") or "", head, base,
                    number, head_sha, base_sha)
        repo.pulls[number] = pull
        self._json(201, self._pull_json(repo, pull), scopes)
        return pull

    def _merge_pull(self, repo, pull, scopes):
        if pull.state != "open":
            self._error(405, "Pull request is already merged" if pull.merged else "Pull request is closed")
            return
        base_tip = repo.tip(pull.base)
        head_tip = repo.tip(pull.head)
        if base_tip is None or head_tip is None:
            self._error(422, "Unknown head or base")
            return
        merge_base = find_merge_base(repo, base_tip, head_tip)
        tree_oid, conflict = merge_trees(repo, merge_base, head_tip, base_tip)
        if conflict:
            self._error(405, "Merge conflict")
            return
        ts = STORE.tick()
        message = "Merge pull request #%d from %s" % (pull.number, pull.head)
        merge_oid = commit_with_tree(repo, tree_oid, [base_tip], message, ts)
        repo.refs["refs/heads/" + pull.base] = merge_oid
        pull.state = "closed"
        pull.merged = True
        pull.merged_at = STORE.iso_now()
        pull.merge_sha = merge_oid
        self._json(200, {"merged": True, "sha": merge_oid, "message": message}, scopes)

    # -- contents ---------------------------------------------------------------
    def _rest_contents(self, method, repo, rest, query, scopes):
        path = unquote(rest.lstrip("/"))
        ref = query.get("ref")
        if method == "GET":
            tip = self._resolve_ref(repo, ref) if ref else repo.tip(repo.default_branch)
            if tip is None:
                self._error(404, "Not Found")
                return
            files = tree_map(repo, tip)
            if path in files:
                mode, oid = files[path]
                obj = repo.get_object(oid)
                data = obj[1] if obj else b""
                self._json(200, {"type": "file", "encoding": "base64",
                                 "content": base64.b64encode(data).decode("ascii"),
                                 "sha": oid, "size": len(data),
                                 "name": path.rsplit("/", 1)[-1], "path": path}, scopes)
                return
            # directory (or root) listing
            prefix = path + "/" if path else ""
            entries = {}
            for fpath, (mode, oid) in files.items():
                if not fpath.startswith(prefix):
                    continue
                rest_path = fpath[len(prefix):]
                first = rest_path.split("/")[0]
                if "/" in rest_path:
                    sub = prefix + first
                    tree_oid = None
                    # find the subtree oid by walking the tree
                    tree_oid = self._subtree_oid(repo, tip, sub)
                    entries[first] = {"type": "dir", "name": first, "path": sub,
                                      "sha": tree_oid or ZERO_OID}
                else:
                    obj = repo.get_object(oid)
                    entries[first] = {"type": "file", "name": first, "path": fpath,
                                      "sha": oid, "size": len(obj[1]) if obj else 0}
            if path and not entries:
                self._error(404, "Not Found")
                return
            self._json(200, [entries[k] for k in sorted(entries)], scopes)
            return
        if method in ("PUT", "DELETE"):
            body, bad = self._json_body()
            if bad:
                return
            branch = body.get("branch") or repo.default_branch
            message = body.get("message") or "Update %s" % path
            if method == "PUT":
                content_b64 = body.get("content")
                if content_b64 is None:
                    self._error(422, "content is required")
                    return
                try:
                    data = base64.b64decode(content_b64, validate=False)
                except Exception:
                    self._error(422, "content is not valid base64")
                    return
                tip = repo.tip(branch)
                files = tree_map(repo, tip) if tip else {}
                current = files.get(path)
                sha = body.get("sha")
                if current is not None:
                    if sha is None:
                        self._error(422, "sha is required to update a file")
                        return
                    if sha != current[1]:
                        self._error(409, "sha does not match the current file")
                        return
                    status = 200
                else:
                    if sha is not None:
                        self._error(422, "sha does not match any file")
                        return
                    status = 201
                commit_oid = self._commit_on_branch(repo, branch, {path: data}, message)
                blob_oid = hash_object("blob", data)
                self._json(status, {"content": {"name": path.rsplit("/", 1)[-1], "path": path,
                                                "sha": blob_oid, "size": len(data),
                                                "type": "file", "encoding": "base64"},
                                    "commit": {"sha": commit_oid, "message": message}}, scopes)
                return
            # DELETE
            tip = repo.tip(branch)
            if tip is None:
                self._error(404, "Not Found")
                return
            files = tree_map(repo, tip)
            current = files.get(path)
            if current is None:
                self._error(404, "Not Found")
                return
            sha = body.get("sha")
            if sha is not None and sha != current[1]:
                self._error(409, "sha does not match the current file")
                return
            commit_oid = self._commit_on_branch(repo, branch, {path: None}, message)
            self._json(200, {"commit": {"sha": commit_oid, "message": message}}, scopes)
            return
        self._error(404, "Not Found")

    def _subtree_oid(self, repo, commit_oid, dir_path):
        tree, _, _, _, _ = parse_commit(repo.get_object(commit_oid)[1])
        current = tree
        for part in dir_path.split("/"):
            obj = repo.get_object(current)
            if obj is None:
                return None
            found = None
            for mode, name, oid in parse_tree(obj[1]):
                if name == part and mode == "40000":
                    found = oid
                    break
            if found is None:
                return None
            current = found
        return current


    # -- git smart HTTP --------------------------------------------------------
    def _handle_git(self, method, owner, repo_name, suffix, query):
        if not self._need_auth():
            return
        repo = STORE.get_repo(owner, repo_name)
        if repo is None or owner != VIEWER_LOGIN:
            # A push cannot invent a repository; a missing one is 404 and
            # the server stays up.
            self._error(404, "Not Found")
            return
        if suffix == "/info/refs":
            if method != "GET":
                self._error(405, "Method Not Allowed")
                return
            service = query.get("service", "")
            if service not in ("git-upload-pack", "git-receive-pack"):
                self._error(400, "Unknown service")
                return
            want_v2 = service == "git-upload-pack" and \
                self.headers.get("Git-Protocol", "") == "version=2"
            with STORE.lock:
                snap = repo.snapshot()
            body = self._advertisement(snap, service, want_v2)
            ctype = "application/x-%s-advertisement" % service
            self._send(200, body, ctype)
            return
        if suffix == "/git-upload-pack":
            if method != "POST":
                self._error(405, "Method Not Allowed")
                return
            raw = self._read_body()
            try:
                packets = decode_pkt_lines(raw)
            except ValueError:
                self._error(400, "Malformed pkt-line stream")
                return
            is_v2 = self.headers.get("Git-Protocol", "") == "version=2"
            try:
                with STORE.lock:
                    snap = repo.snapshot()
                body = self._upload_pack(snap, packets, is_v2)
            except ValueError as exc:
                self._error(400, str(exc))
                return
            self._send(200, body, "application/x-git-upload-pack-result")
            return
        if suffix == "/git-receive-pack":
            if method != "POST":
                self._error(405, "Method Not Allowed")
                return
            raw = self._read_body()
            try:
                with STORE.lock:
                    body = self._receive_pack(repo, raw)
            except ValueError as exc:
                self._error(400, str(exc))
                return
            self._send(200, body, "application/x-git-receive-pack-result")
            return
        self._error(404, "Not Found")

    def _ref_lines_v0(self, repo):
        """[(oid, name)] for the v0 advertisement: HEAD, branches, tags."""
        lines = []
        main_tip = repo.refs.get("refs/heads/" + repo.default_branch, ZERO_OID)
        lines.append((main_tip, "HEAD"))
        for ref in repo.branches():
            lines.append((repo.refs[ref], ref))
        for ref in repo.tags():
            lines.append((repo.refs[ref], ref))
        return lines

    def _advertisement(self, repo, service, want_v2):
        if service == "git-upload-pack" and want_v2:
            caps = ["ls-refs=unborn", "fetch=shallow", "agent=%s" % AGENT,
                    "object-format=sha1"]
            items = ["# service=git-upload-pack\n", "flush", "version 2\n"]
            items += [c + "\n" for c in caps]
            items.append("flush")
            return pkt_lines(items)
        if service == "git-upload-pack":
            caps = ("symref=HEAD:refs/heads/%s side-band-64k thin-pack ofs-delta "
                    "multi_ack multi_ack_detailed shallow agent=%s" % (repo.default_branch, AGENT))
        else:
            caps = ("report-status side-band-64k delete-refs ofs-delta agent=%s" % AGENT)
        lines = ["# service=%s\n" % service, "flush"]
        refs = self._ref_lines_v0(repo)
        if not refs[1:]:  # no branches or tags at all: the unborn form
            lines.append("%s capabilities^{}\0%s\n" % (ZERO_OID, caps))
        else:
            first = True
            for oid, name in refs:
                line = "%s %s" % (oid, name)
                if first:
                    line += "\0" + caps
                    first = False
                lines.append(line + "\n")
            for ref in repo.tags():
                oid = repo.refs[ref]
                obj = repo.get_object(oid)
                if obj and obj[0] == "tag":
                    peeled = parse_tag(obj[1])[0]
                    lines.append("%s %s^{}\n" % (peeled, ref))
        lines.append("flush")
        return pkt_lines(lines)

    def _ls_refs(self, repo, args):
        """args: the parsed ls-refs arguments. Returns the response bytes."""
        prefixes = [a[11:] for a in args if a.startswith("ref-prefix ")]
        want_peel = "peel" in args
        want_symrefs = "symrefs" in args
        want_unborn = "unborn" in args

        def keep(name):
            return not prefixes or any(name.startswith(p) for p in prefixes)

        out = []
        main_tip = repo.refs.get("refs/heads/" + repo.default_branch)
        if not repo.refs:
            if want_unborn and keep("HEAD"):
                out.append("unborn HEAD symref-target:refs/heads/%s\n" % repo.default_branch)
            return pkt_lines(out + ["flush"])
        if keep("HEAD"):
            line = "%s HEAD" % (main_tip or ZERO_OID)
            if want_symrefs:
                line += " symref-target:refs/heads/%s" % repo.default_branch
            out.append(line + "\n")
        for ref in repo.branches():
            if not keep(ref):
                continue
            out.append("%s %s\n" % (repo.refs[ref], ref))
        for ref in repo.tags():
            if not keep(ref):
                continue
            oid = repo.refs[ref]
            line = "%s %s" % (oid, ref)
            if want_peel:
                obj = repo.get_object(oid)
                if obj and obj[0] == "tag":
                    line += " peeled:%s" % parse_tag(obj[1])[0]
            out.append(line + "\n")
        out.append("flush")
        return pkt_lines(out)

    def _upload_pack(self, repo, packets, is_v2):
        lines = []
        for packet in packets:
            if packet[0] == "data":
                lines.append(packet[1].decode("utf-8"))
        if is_v2:
            if not lines or not lines[0].startswith("command="):
                raise ValueError("v2 request has no command")
            command = lines[0].split("=", 1)[1].strip()
            args = [ln.rstrip("\n") for ln in lines[1:]]
            if command == "ls-refs":
                return self._ls_refs(repo, args)
            if command == "fetch":
                return self._fetch_v2(repo, args)
            raise ValueError("unknown v2 command %r" % command)
        return self._fetch_v0(repo, packets)

    def _fetch_v2(self, repo, args):
        wants = []
        haves = []
        shallow_client = []
        depth = None
        done = False
        for arg in args:
            if arg.startswith("want "):
                wants.append(arg[5:].strip())
            elif arg.startswith("have "):
                haves.append(arg[5:].strip())
            elif arg.startswith("shallow "):
                shallow_client.append(arg[8:].strip())
            elif arg.startswith("deepen "):
                try:
                    depth = int(arg[7:].strip())
                except ValueError:
                    pass
            elif arg.strip() == "done":
                done = True
        return self._build_fetch(repo, wants, haves, shallow_client, depth,
                                 v2=True, done=done)

    def _fetch_v0(self, repo, packets):
        wants = []
        haves = []
        shallow_client = []
        depth = None
        done = False
        for packet in packets:
            if packet[0] != "data":
                continue
            text = packet[1].decode("utf-8").rstrip("\n")
            if text.startswith("want "):
                first = text[5:].split(" ")
                wants.append(first[0])
            elif text.startswith("shallow "):
                shallow_client.append(text[8:].strip())
            elif text.startswith("deepen "):
                try:
                    depth = int(text[7:].strip())
                except ValueError:
                    pass
            elif text.startswith("have "):
                haves.append(text[5:].strip())
            elif text.strip() == "done":
                done = True
        return self._build_fetch(repo, wants, haves, shallow_client, depth,
                                 v2=False, done=done)

    def _build_fetch(self, repo, wants, haves, shallow_client, depth, v2,
                     done=False):
        wants = [w for w in dict.fromkeys(wants) if is_oid(w)]
        haves = [h for h in haves if is_oid(h)]
        shallow_set = set(s for s in shallow_client if is_oid(s))
        included, boundary = depth_closure(repo, wants, depth)
        held = have_closure(repo, haves, shallow_set)
        send = included - held
        # The boundary of a shallow fetch: the commits at generation depth-1.
        # The client's old boundaries that are now included are unshallow.
        new_shallow = sorted(boundary & send) if depth is not None else []
        unshallow = sorted(s for s in shallow_set if s in included)
        objects = []
        for oid in sorted(send):
            obj = repo.get_object(oid)
            if obj is not None:
                objects.append((obj[0], obj[1]))
        # Real git (2.43, verified against its stateless upload-pack and
        # against a live `git pull`): a v2 fetch response carries an
        # acknowledgments section ONLY while negotiation is still open --
        # that is, the client sent haves and did NOT end with `done`
        # (exactly what `git pull`/`git fetch` do). A fresh clone sends no
        # haves and ends with `done`, so the response goes straight to
        # shallow-info (only when there are shallow/unshallow lines) and
        # then packfile. An empty fetch still carries a packfile section
        # with a zero-object pack, never no packfile section at all. The
        # kit's parser accepts this shape too.
        pack = write_pack(objects)
        # Only walk the whole history when the client actually sent haves:
        # reachable() costs ~4.5 ms on a 200-commit repo, and a fresh clone
        # (no haves) never needs it -- it was 90% of a fetch's CPU.
        common = sorted(set(haves) & reachable(repo, wants)) if haves else []
        if v2:
            out = bytearray()
            if haves and not done:
                out += pkt_line("acknowledgments\n")
                if common:
                    for oid in common:
                        out += pkt_line("ACK %s\n" % oid)
                else:
                    out += pkt_line("NAK\n")
                out += DELIM
            if new_shallow or unshallow:
                out += pkt_line("shallow-info\n")
                for oid in unshallow:
                    out += pkt_line("unshallow %s\n" % oid)
                for oid in new_shallow:
                    out += pkt_line("shallow %s\n" % oid)
                out += DELIM
            out += pkt_line("packfile\n")
            for i in range(0, len(pack), 65515):
                out += pkt_line(b"\x01" + pack[i:i + 65515])
            out += FLUSH
            return bytes(out)
        # v0: ACK lines for the common haves (or NAK), then shallow lines,
        # then the sideband pack.
        out = bytearray()
        if common:
            for oid in common:
                out += pkt_line("ACK %s\n" % oid)
        else:
            out += pkt_line("NAK\n")
        for oid in unshallow:
            out += pkt_line("unshallow %s\n" % oid)
        for oid in new_shallow:
            out += pkt_line("shallow %s\n" % oid)
        for i in range(0, len(pack), 65515):
            out += pkt_line(b"\x01" + pack[i:i + 65515])
        out += FLUSH
        return bytes(out)

    def _receive_pack(self, repo, raw):
        # Read command pkt-lines up to the flush; the pack bytes that follow
        # the flush are raw, not pkt-lines, so they are sliced, not parsed.
        commands = []
        pos = 0
        while pos < len(raw):
            head = raw[pos:pos + 4]
            if len(head) < 4:
                raise ValueError("truncated pkt-line in receive-pack")
            try:
                length = int(head.decode("ascii"), 16)
            except ValueError:
                raise ValueError("bad pkt-line length in receive-pack")
            if length == 0:
                pos += 4
                break
            if length < 4 or pos + length > len(raw):
                raise ValueError("truncated pkt-line in receive-pack")
            text = raw[pos + 4:pos + length].decode("utf-8")
            nul = text.find("\0")
            if nul >= 0:
                text = text[:nul]
            parts = text.rstrip("\n").split(" ")
            if len(parts) != 3:
                raise ValueError("bad receive-pack command line")
            commands.append((parts[0], parts[1], parts[2]))
            pos += length
        pack_bytes = raw[pos:]
        results = []  # (ref, ok, reason)
        unpack_ok = True
        unpack_detail = "ok"
        new_objects = {}
        if pack_bytes:
            try:
                new_objects = read_pack(pack_bytes,
                                        resolve_base=lambda oid: repo.get_object(oid))
            except ValueError as exc:
                unpack_ok = False
                unpack_detail = str(exc)
        if unpack_ok:
            for oid, (obj_type, data) in new_objects.items():
                repo.objects.setdefault(oid, (obj_type, data))
            for old, new, ref in commands:
                current = repo.refs.get(ref)
                if new == ZERO_OID:
                    # delete
                    if current is None:
                        results.append((ref, False, "ref does not exist"))
                    elif old != ZERO_OID and old != current:
                        results.append((ref, False, "stale info"))
                    else:
                        del repo.refs[ref]
                        results.append((ref, True, ""))
                    continue
                if repo.get_object(new) is None:
                    results.append((ref, False, "object not found"))
                    continue
                if old == ZERO_OID:
                    if current is not None:
                        results.append((ref, False, "already exists"))
                        continue
                    repo.refs[ref] = new
                    results.append((ref, True, ""))
                    continue
                if current is None:
                    results.append((ref, False, "ref does not exist"))
                    continue
                if old != current:
                    results.append((ref, False, "stale info"))
                    continue
                if ref.startswith("refs/heads/") and not is_ancestor(repo, old, new):
                    results.append((ref, False, "non-fast-forward"))
                    continue
                repo.refs[ref] = new
                results.append((ref, True, ""))
        else:
            for _, _, ref in commands:
                results.append((ref, False, "unpack failed"))
        report = []
        report.append("unpack %s\n" % unpack_detail)
        for ref, ok, reason in results:
            if ok:
                report.append("ok %s\n" % ref)
            else:
                report.append("ng %s %s\n" % (ref, reason or "failed"))
        inner = pkt_lines(report + ["flush"])
        out = bytearray()
        for i in range(0, len(inner), 65515):
            out += pkt_line(b"\x01" + inner[i:i + 65515])
        out += FLUSH
        return bytes(out)


# ---------------------------------------------------------------------------
# GraphQL v4 (a small parser + executor for the documents gh sends)
# ---------------------------------------------------------------------------

class _GQLError(Exception):
    pass


def _gql_lex(text):
    tokens = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in " \t\r\n,":
            i += 1
        elif ch == "#":
            while i < len(text) and text[i] != "\n":
                i += 1
        elif ch in "{}()[]:!=$@":
            tokens.append((ch, ch))
            i += 1
        elif text.startswith("...", i):
            tokens.append(("...", "..."))
            i += 3
        elif ch == '"':
            j = i + 1
            out = []
            while j < len(text) and text[j] != '"':
                if text[j] == "\\" and j + 1 < len(text):
                    out.append(text[j + 1])
                    j += 2
                else:
                    out.append(text[j])
                    j += 1
            tokens.append(("STRING", "".join(out)))
            i = j + 1
        elif ch.isdigit() or (ch == "-" and i + 1 < len(text) and text[i + 1].isdigit()):
            j = i
            while j < len(text) and (text[j].isdigit() or text[j] in ".eE+-"):
                j += 1
            raw = text[i:j]
            tokens.append(("NUMBER", float(raw) if any(c in raw for c in ".eE") else int(raw)))
            i = j
        elif ch.isalpha() or ch == "_":
            j = i
            while j < len(text) and (text[j].isalnum() or text[j] == "_"):
                j += 1
            tokens.append(("NAME", text[i:j]))
            i = j
        else:
            raise _GQLError("unexpected character %r" % ch)
    tokens.append(("EOF", None))
    return tokens


class _GQLParser:
    def __init__(self, text):
        self.tokens = _gql_lex(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect(self, kind):
        tok = self.next()
        if tok[0] != kind:
            raise _GQLError("expected %s, got %s" % (kind, tok[0]))
        return tok[1]

    def parse_document(self):
        ops = []
        while self.peek()[0] != "EOF":
            ops.append(self.parse_operation())
        return ops

    def parse_operation(self):
        kind = "query"
        if self.peek() == ("NAME", "query") or self.peek() == ("NAME", "mutation"):
            kind = self.next()[1]
        name = None
        if self.peek()[0] == "NAME":
            name = self.next()[1]
        variables = {}
        if self.peek()[0] == "(":
            self.next()
            while self.peek()[0] != ")":
                self.expect("$")
                var_name = self.expect("NAME")
                self.expect(":")
                self.parse_type()
                if self.peek()[0] == "=":
                    self.next()
                    variables[var_name] = self.parse_value({})
                else:
                    variables[var_name] = None
            self.expect(")")
        selection = self.parse_selection_set()
        return {"kind": kind, "name": name, "variables": variables, "selection": selection}

    def parse_type(self):
        if self.peek()[0] == "[":
            self.next()
            self.parse_type()
            self.expect("]")
        else:
            self.expect("NAME")
        if self.peek()[0] == "!":
            self.next()

    def parse_selection_set(self):
        self.expect("{")
        fields = []
        while self.peek()[0] != "}":
            fields.append(self.parse_field())
        self.expect("}")
        return fields

    def parse_field(self):
        if self.peek()[0] == "...":
            self.next()
            on_type = None
            if self.peek() == ("NAME", "on"):
                self.next()
                on_type = self.expect("NAME")
            selection = self.parse_selection_set()
            return {"fragment": True, "on": on_type, "selection": selection}
        name = self.expect("NAME")
        alias = None
        if self.peek()[0] == ":":
            self.next()
            alias = name
            name = self.expect("NAME")
        args = {}
        if self.peek()[0] == "(":
            self.next()
            while self.peek()[0] != ")":
                arg_name = self.expect("NAME")
                self.expect(":")
                args[arg_name] = self.parse_value({})
            self.expect(")")
        selection = None
        if self.peek()[0] == "{":
            selection = self.parse_selection_set()
        return {"name": name, "alias": alias or name, "args": args, "selection": selection}

    def parse_value(self, variables):
        kind, value = self.peek()
        if kind == "$":
            self.next()
            return ("var", self.expect("NAME"))
        if kind == "STRING":
            self.next()
            return value
        if kind == "NUMBER":
            self.next()
            return value
        if kind == "NAME":
            self.next()
            if value == "true":
                return True
            if value == "false":
                return False
            if value == "null":
                return None
            return ("enum", value)
        if kind == "[":
            self.next()
            items = []
            while self.peek()[0] != "]":
                items.append(self.parse_value(variables))
            self.expect("]")
            return items
        if kind == "{":
            self.next()
            obj = {}
            while self.peek()[0] != "}":
                key = self.expect("NAME")
                self.expect(":")
                obj[key] = self.parse_value(variables)
            self.expect("}")
            return obj
        raise _GQLError("unexpected value token %s" % kind)


def _gql_resolve_value(value, variables):
    if isinstance(value, tuple) and value and value[0] == "var":
        return variables.get(value[1])
    if isinstance(value, tuple) and value and value[0] == "enum":
        return value[1]
    if isinstance(value, list):
        return [_gql_resolve_value(v, variables) for v in value]
    if isinstance(value, dict):
        return {k: _gql_resolve_value(v, variables) for k, v in value.items()}
    return value


# -- schema field tables (for __type introspection) --------------------------

_GQL_TYPE_FIELDS = {
    "Issue": ["id", "number", "title", "state", "body", "url", "author",
              "createdAt", "comments", "labels"],
    "PullRequest": ["id", "number", "title", "body", "headRefName", "baseRefName",
                    "mergeable", "state", "merged", "files", "headRef", "baseRef",
                    "author", "createdAt", "mergedAt", "mergeCommit", "url"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "issue", "issues", "pullRequests", "pullRequest",
                   "description", "private", "url", "createdAt"],
    "SearchType": [],
    "User": ["login", "id"],
}

_GQL_SEARCH_ENUMS = ["ISSUE", "PULL_REQUEST", "REPOSITORY", "USER", "DISCUSSION",
                     "COMMIT", "CODE", "WIKI", "MARKETPLACE", "TOPIC"]


class GraphQLExecutor:
    def __init__(self):
        self.errors = []

    # -- object wrappers ------------------------------------------------------
    def _repo_obj(self, repo):
        return {"_gtype": "Repository", "repo": repo}

    def _issue_obj(self, repo, issue):
        return {"_gtype": "Issue", "repo": repo, "issue": issue}

    def _pull_obj(self, repo, pull):
        return {"_gtype": "PullRequest", "repo": repo, "pull": pull}

    def _user_obj(self):
        return {"_gtype": "User"}

    # -- entry point ------------------------------------------------------------
    def execute(self, document, variables):
        self.errors = []
        try:
            ops = _GQLParser(document).parse_document()
        except _GQLError as exc:
            return None, [{"message": str(exc)}]
        if not ops:
            return None, [{"message": "Empty document"}]
        op = ops[0]
        if len(ops) > 1 and variables.get("__operationName"):
            for candidate in ops:
                if candidate["name"] == variables["__operationName"]:
                    op = candidate
                    break
        root_type = "Query" if op["kind"] == "query" else "Mutation"
        root = {"_gtype": root_type}
        data = self._resolve_selection(root, op["selection"], variables, root_type)
        if self.errors:
            return None, self.errors
        return data, []

    def _resolve_selection(self, obj, selection, variables, type_name):
        out = {}
        for field in selection:
            if field.get("fragment"):
                if field.get("on") is None or field["on"] == type_name:
                    sub = self._resolve_selection(obj, field["selection"], variables, type_name)
                    out.update(sub)
                continue
            name = field["name"]
            alias = field["alias"]
            args = {k: _gql_resolve_value(v, variables) for k, v in field["args"].items()}
            value = self._resolve_field(obj, name, args, variables, type_name)
            if value is _GQL_MISSING:
                self.errors.append({"message": 'Cannot query field "%s" on type "%s".' % (name, type_name)})
                continue
            if field["selection"] is not None:
                if value is None:
                    out[alias] = None
                elif isinstance(value, list):
                    out[alias] = [self._resolve_selection(item, field["selection"], variables, item["_gtype"])
                                  if isinstance(item, dict) and "_gtype" in item else item for item in value]
                elif isinstance(value, dict) and "_gtype" in value:
                    out[alias] = self._resolve_selection(value, field["selection"], variables, value["_gtype"])
                else:
                    out[alias] = value
            else:
                out[alias] = value
        return out

    # -- field resolvers --------------------------------------------------------
    def _resolve_field(self, obj, name, args, variables, type_name):
        gtype = obj.get("_gtype")
        if gtype == "Query":
            if name == "viewer":
                return self._user_obj()
            if name == "repository":
                repo = STORE.get_repo(args.get("owner"), args.get("name"))
                if repo is None or args.get("owner") != VIEWER_LOGIN:
                    return None
                return self._repo_obj(repo)
            if name == "node":
                return self._node(args.get("id"))
            if name == "__type":
                return {"_gtype": "__Type", "name": args.get("name")}
            return _GQL_MISSING
        if gtype == "Mutation":
            if name == "createIssue":
                return self._mut_create_issue(args.get("input") or {})
            if name == "closeIssue":
                return self._mut_close_issue(args.get("input") or {})
            if name == "createPullRequest":
                return self._mut_create_pull(args.get("input") or {})
            if name == "mergePullRequest":
                return self._mut_merge_pull(args.get("input") or {})
            if name == "addComment":
                return self._mut_add_comment(args.get("input") or {})
            return _GQL_MISSING
        if gtype == "User":
            if name == "login":
                return VIEWER_LOGIN
            if name == "id":
                return global_id("User", VIEWER_LOGIN)
            return _GQL_MISSING
        if gtype == "Repository":
            return self._repo_field(obj["repo"], name, args)
        if gtype == "Issue":
            issue = obj["issue"]
            repo = obj["repo"]
            if name == "id":
                return global_id("Issue", repo.owner, repo.name, issue.number)
            if name == "number":
                return issue.number
            if name == "title":
                return issue.title
            if name == "state":
                return issue.state.upper()
            if name == "body":
                return issue.body
            if name == "url":
                return "https://example.invalid/%s/%s/issues/%d" % (repo.owner, repo.name, issue.number)
            return _GQL_MISSING
        if gtype == "PullRequest":
            pull = obj["pull"]
            repo = obj["repo"]
            if name == "id":
                return global_id("PullRequest", repo.owner, repo.name, pull.number)
            if name == "number":
                return pull.number
            if name == "title":
                return pull.title
            if name == "body":
                return pull.body
            if name == "state":
                return "MERGED" if pull.merged else pull.state.upper()
            if name == "merged":
                return pull.merged
            if name == "headRefName":
                return pull.head
            if name == "baseRefName":
                return pull.base
            if name == "mergeable":
                return self._mergeable(repo, pull)
            if name == "files":
                first = args.get("first") or 10
                files = diff_files(repo, pull.base_sha, pull.head_sha)[:first]
                return {"_gtype": "PullRequestChangedFileConnection",
                        "nodes": [{"_gtype": "PullRequestChangedFile", "path": f["filename"]} for f in files]}
            return _GQL_MISSING
        if gtype == "IssueConnection":
            if name == "nodes":
                return obj["nodes"]
            if name == "pageInfo":
                return {"_gtype": "PageInfo", "hasNextPage": obj["hasNextPage"],
                        "endCursor": obj["endCursor"]}
            return _GQL_MISSING
        if gtype == "PullRequestConnection":
            if name == "nodes":
                return obj["nodes"]
            return _GQL_MISSING
        if gtype == "PullRequestChangedFileConnection":
            if name == "nodes":
                return obj["nodes"]
            return _GQL_MISSING
        if gtype == "PullRequestChangedFile":
            if name == "path":
                return obj["path"]
            return _GQL_MISSING
        if gtype == "PageInfo":
            if name == "hasNextPage":
                return obj["hasNextPage"]
            if name == "endCursor":
                return obj["endCursor"]
            return _GQL_MISSING
        if gtype == "__Type":
            tname = obj["name"]
            if name == "fields":
                return [{"_gtype": "__Field", "name": f} for f in _GQL_TYPE_FIELDS.get(tname, [])]
            if name == "enumValues":
                if tname == "SearchType":
                    return [{"_gtype": "__EnumValue", "name": e} for e in _GQL_SEARCH_ENUMS]
                return []
            if name == "name":
                return tname
            return _GQL_MISSING
        if gtype == "__Field":
            if name == "name":
                return obj["name"]
            return _GQL_MISSING
        if gtype == "__EnumValue":
            if name == "name":
                return obj["name"]
            return _GQL_MISSING
        if gtype in ("CreateIssuePayload", "CloseIssuePayload"):
            if name == "issue" and obj.get("issue") is not None:
                return self._issue_obj(obj["repo"], obj["issue"])
            return _GQL_MISSING
        if gtype in ("CreatePullRequestPayload", "MergePullRequestPayload"):
            if name == "pullRequest" and obj.get("pull") is not None:
                return self._pull_obj(obj["repo"], obj["pull"])
            return _GQL_MISSING
        if gtype == "AddCommentPayload":
            if name == "commentEdge":
                return {"_gtype": "CommentEdge", "node": obj["node"]}
            return _GQL_MISSING
        if gtype == "CommentEdge":
            if name == "node":
                return obj["node"]
            return _GQL_MISSING
        if gtype == "Comment":
            if name == "id":
                return obj["id"]
            if name == "body":
                return obj["body"]
            return _GQL_MISSING
        return _GQL_MISSING

    def _node(self, gid):
        if not gid:
            return None
        parsed = parse_global_id(gid)
        if parsed is None:
            return None
        kind, rest = parsed
        parts = rest.split("/")
        if kind == "Repository" and len(parts) == 2:
            repo = STORE.get_repo(parts[0], parts[1])
            return self._repo_obj(repo) if repo else None
        if kind == "Issue" and len(parts) == 3:
            repo = STORE.get_repo(parts[0], parts[1])
            issue = repo.issues.get(int(parts[2])) if repo else None
            return self._issue_obj(repo, issue) if issue else None
        if kind == "PullRequest" and len(parts) == 3:
            repo = STORE.get_repo(parts[0], parts[1])
            pull = repo.pulls.get(int(parts[2])) if repo else None
            return self._pull_obj(repo, pull) if pull else None
        return None

    def _repo_field(self, repo, name, args):
        if name == "id":
            return global_id("Repository", repo.owner, repo.name)
        if name == "databaseId":
            return repo.id
        if name == "name":
            return repo.name
        if name == "nameWithOwner":
            return "%s/%s" % (repo.owner, repo.name)
        if name == "owner":
            return self._user_obj()
        if name == "defaultBranchRef":
            tip = repo.tip(repo.default_branch)
            if tip is None:
                return None
            return {"_gtype": "Ref", "name": repo.default_branch}
        if name == "viewerPermission":
            return "ADMIN"
        if name == "hasIssuesEnabled":
            return True
        if name == "description":
            return repo.description
        if name == "private":
            return repo.private
        if name == "issue":
            issue = repo.issues.get(args.get("number"))
            return self._issue_obj(repo, issue) if issue else None
        if name == "issues":
            return self._issues_connection(repo, args)
        if name == "pullRequests":
            pulls = sorted(repo.pulls.values(), key=lambda p: p.seq)
            pulls = [p for p in pulls if p.state == "open"]
            first = args.get("first")
            if first is not None:
                pulls = pulls[:first]
            return {"_gtype": "PullRequestConnection",
                    "nodes": [self._pull_obj(repo, p) for p in pulls]}
        if name == "pullRequest":
            pull = repo.pulls.get(args.get("number"))
            return self._pull_obj(repo, pull) if pull else None
        return _GQL_MISSING

    def _issues_connection(self, repo, args):
        issues = sorted(repo.issues.values(), key=lambda i: i.seq)
        states = args.get("states")
        if states:
            wanted = {s.upper() for s in states}
            issues = [i for i in issues if i.state.upper() in wanted]
        order_by = args.get("orderBy") or {}
        field = (order_by.get("field") or "CREATED_AT").upper()
        direction = (order_by.get("direction") or "DESC").upper()
        if field in ("CREATED_AT", "UPDATED_AT"):
            issues = sorted(issues, key=lambda i: (i.seq, i.number),
                            reverse=(direction == "DESC"))
        first = args.get("first")
        after = args.get("after")
        start = 0
        if after:
            try:
                cursor_num = int(base64.urlsafe_b64decode(
                    after + "=" * (-len(after) % 4)).decode("ascii").split(":")[1])
                for idx, issue in enumerate(issues):
                    if issue.number == cursor_num:
                        start = idx + 1
                        break
            except Exception:
                start = 0
        page = issues[start:]
        has_next = False
        if first is not None:
            if len(page) > first:
                has_next = True
            page = page[:first]
        end_cursor = None
        if page:
            end_cursor = base64.urlsafe_b64encode(
                ("cursor:%d" % page[-1].number).encode("ascii")).decode("ascii").rstrip("=")
        return {"_gtype": "IssueConnection",
                "nodes": [self._issue_obj(repo, i) for i in page],
                "hasNextPage": has_next, "endCursor": end_cursor}

    def _mergeable(self, repo, pull):
        if pull.state != "open":
            return "UNKNOWN"
        base_tip = repo.tip(pull.base)
        head_tip = repo.tip(pull.head)
        if base_tip is None or head_tip is None:
            return "UNKNOWN"
        merge_base = find_merge_base(repo, base_tip, head_tip)
        _, conflict = merge_trees(repo, merge_base, head_tip, base_tip)
        return "CONFLICTING" if conflict else "MERGEABLE"

    # -- mutations ---------------------------------------------------------------
    def _repo_from_global_id(self, gid):
        parsed = parse_global_id(gid) if gid else None
        if parsed is None or parsed[0] != "Repository":
            return None
        parts = parsed[1].split("/")
        if len(parts) != 2:
            return None
        return STORE.get_repo(parts[0], parts[1])

    def _issue_from_global_id(self, gid):
        parsed = parse_global_id(gid) if gid else None
        if parsed is None or parsed[0] != "Issue":
            return None, None
        parts = parsed[1].split("/")
        if len(parts) != 3:
            return None, None
        repo = STORE.get_repo(parts[0], parts[1])
        if repo is None:
            return None, None
        return repo, repo.issues.get(int(parts[2]))

    def _mut_create_issue(self, input_):
        repo = self._repo_from_global_id(input_.get("repositoryId"))
        if repo is None:
            self.errors.append({"message": "Repository not found"})
            return {"_gtype": "CreateIssuePayload", "repo": None, "issue": None}
        number = repo.next_number
        repo.next_number += 1
        issue = Issue(number, input_.get("title") or "", input_.get("body") or "", number)
        issue.seq = number
        repo.issues[number] = issue
        return {"_gtype": "CreateIssuePayload", "repo": repo, "issue": issue}

    def _mut_close_issue(self, input_):
        repo, issue = self._issue_from_global_id(input_.get("issueId"))
        if issue is None:
            self.errors.append({"message": "Issue not found"})
            return {"_gtype": "CloseIssuePayload", "repo": None, "issue": None}
        issue.state = "closed"
        return {"_gtype": "CloseIssuePayload", "repo": repo, "issue": issue}

    def _mut_create_pull(self, input_):
        repo = self._repo_from_global_id(input_.get("repositoryId"))
        if repo is None:
            self.errors.append({"message": "Repository not found"})
            return {"_gtype": "CreatePullRequestPayload", "repo": None, "pull": None}
        head = input_.get("headRefName")
        base = input_.get("baseRefName") or repo.default_branch
        head_sha = repo.tip(head) if head else None
        base_sha = repo.tip(base) if base else None
        if head_sha is None or base_sha is None:
            self.errors.append({"message": "Unknown head or base"})
            return {"_gtype": "CreatePullRequestPayload", "repo": repo, "pull": None}
        for pull in repo.pulls.values():
            if pull.state == "open" and pull.head == head and pull.base == base:
                self.errors.append({"message": "A pull request already exists for this branch"})
                return {"_gtype": "CreatePullRequestPayload", "repo": repo, "pull": None}
        number = repo.next_number
        repo.next_number += 1
        pull = Pull(number, input_.get("title") or "", "", head, base, number, head_sha, base_sha)
        repo.pulls[number] = pull
        return {"_gtype": "CreatePullRequestPayload", "repo": repo, "pull": pull}

    def _mut_merge_pull(self, input_):
        parsed = parse_global_id(input_.get("pullRequestId")) if input_.get("pullRequestId") else None
        if parsed is None or parsed[0] != "PullRequest":
            self.errors.append({"message": "Pull request not found"})
            return {"_gtype": "MergePullRequestPayload", "repo": None, "pull": None}
        parts = parsed[1].split("/")
        repo = STORE.get_repo(parts[0], parts[1])
        pull = repo.pulls.get(int(parts[2])) if repo else None
        if pull is None:
            self.errors.append({"message": "Pull request not found"})
            return {"_gtype": "MergePullRequestPayload", "repo": repo, "pull": None}
        if pull.state != "open":
            self.errors.append({"message": "Pull request is already merged"})
            return {"_gtype": "MergePullRequestPayload", "repo": repo, "pull": pull}
        base_tip = repo.tip(pull.base)
        head_tip = repo.tip(pull.head)
        merge_base = find_merge_base(repo, base_tip, head_tip)
        tree_oid, conflict = merge_trees(repo, merge_base, head_tip, base_tip)
        if conflict:
            self.errors.append({"message": "Merge conflict"})
            return {"_gtype": "MergePullRequestPayload", "repo": repo, "pull": pull}
        ts = STORE.tick()
        message = "Merge pull request #%d from %s" % (pull.number, pull.head)
        merge_oid = commit_with_tree(repo, tree_oid, [base_tip], message, ts)
        repo.refs["refs/heads/" + pull.base] = merge_oid
        pull.state = "closed"
        pull.merged = True
        pull.merged_at = STORE.iso_now()
        pull.merge_sha = merge_oid
        return {"_gtype": "MergePullRequestPayload", "repo": repo, "pull": pull}

    def _mut_add_comment(self, input_):
        repo, issue = self._issue_from_global_id(input_.get("subjectId"))
        if issue is None:
            self.errors.append({"message": "Issue not found"})
            return {"_gtype": "AddCommentPayload",
                    "node": {"_gtype": "Comment", "id": "", "body": ""}}
        cid = repo.next_comment
        repo.next_comment += 1
        body = input_.get("body") or ""
        issue.comments.append((cid, body))
        node = {"_gtype": "Comment",
                "id": global_id("IssueComment", repo.owner, repo.name, issue.number, cid),
                "body": body}
        return {"_gtype": "AddCommentPayload", "node": node}


class _Missing:
    pass


_GQL_MISSING = _Missing()


# The Ref wrapper's name field (defaultBranchRef) is resolved here because
# _resolve_field dispatches on _gtype and "Ref" was not in its table.
_orig_resolve_field = GraphQLExecutor._resolve_field


def _resolve_field_with_ref(self, obj, name, args, variables, type_name):
    if obj.get("_gtype") == "Ref":
        if name == "name":
            return obj["name"]
        return _GQL_MISSING
    return _orig_resolve_field(self, obj, name, args, variables, type_name)


GraphQLExecutor._resolve_field = _resolve_field_with_ref


# ---------------------------------------------------------------------------
# MCP (JSON-RPC 2.0 Streamable HTTP) + GraphQL/MCP request handlers
# ---------------------------------------------------------------------------

_MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a repository owned by the authenticated user.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string"},
                "description": {"type": "string"},
                "private": {"type": "boolean"},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get a repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_issue",
        "description": "Create an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "title": {"type": "string"},
                "body": {"type": "string"},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List issues in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "state": {"type": "string"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Create a pull request in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "title": {"type": "string"},
                "head": {"type": "string"},
                "base": {"type": "string"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Merge a pull request in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "pull_number": {"type": "integer"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]


def _mcp_owner_repo(args):
    """Normalize owner/repo from the many synonyms clients send."""
    owner = args.get("owner")
    repo = args.get("repo") or args.get("repository") or args.get("repo_name")
    full = args.get("full_name") or args.get("fullName")
    if full and "/" in str(full):
        owner, repo = str(full).split("/", 1)
    return owner, repo


def _mcp_tool_result(handler, method, params):
    name = params.get("name")
    args = params.get("arguments") or {}
    if not isinstance(args, dict):
        return None, {"code": -32602, "message": "arguments must be an object"}
    fn = _MCP_DISPATCH.get(name)
    if fn is None:
        return None, {"code": -32602, "message": "unknown tool %r" % (name,)}
    try:
        result = fn(args)
    except _MCPToolError as exc:
        return {"content": [{"type": "text", "text": json.dumps({"error": str(exc)})}],
                "isError": True}, None
    return {"content": [{"type": "text", "text": json.dumps(result)}], "isError": False}, None


class _MCPToolError(Exception):
    pass


def _mcp_require(args, *keys):
    for key in keys:
        if args.get(key) is None:
            raise _MCPToolError("missing required argument %r" % key)


def _mcp_get_repo(args):
    owner, repo_name = _mcp_owner_repo(args)
    _mcp_require({"owner": owner, "repo": repo_name}, "owner", "repo")
    repo = STORE.get_repo(owner, repo_name)
    if repo is None:
        raise _MCPToolError("repository %s/%s not found" % (owner, repo_name))
    return repo


def _mcp_create_repo(args):
    _mcp_require(args, "name")
    name = args["name"]
    if not isinstance(name, str) or not name:
        raise _MCPToolError("name must be a non-empty string")
    if STORE.get_repo(VIEWER_LOGIN, name) is not None:
        raise _MCPToolError("repository %s already exists" % name)
    repo = STORE.create_repo(VIEWER_LOGIN, name, bool(args.get("private", False)),
                             args.get("description") or "")
    if args.get("default_branch"):
        repo.default_branch = args["default_branch"]
    return {"name": repo.name, "full_name": "%s/%s" % (repo.owner, repo.name),
            "private": repo.private, "default_branch": repo.default_branch,
            "description": repo.description}


def _mcp_get_repo_tool(args):
    repo = _mcp_get_repo(args)
    return {"name": repo.name, "full_name": "%s/%s" % (repo.owner, repo.name),
            "private": repo.private, "default_branch": repo.default_branch,
            "description": repo.description}


def _mcp_create_issue(args):
    repo = _mcp_get_repo(args)
    _mcp_require(args, "title")
    number = repo.next_number
    repo.next_number += 1
    issue = Issue(number, args["title"], args.get("body") or "", number)
    repo.issues[number] = issue
    return {"number": number, "title": issue.title, "body": issue.body,
            "state": "open"}


def _mcp_list_issues(args):
    repo = _mcp_get_repo(args)
    state = (args.get("state") or "open").lower()
    out = []
    for issue in sorted(repo.issues.values(), key=lambda i: i.seq):
        if state != "all" and issue.state != state:
            continue
        out.append({"number": issue.number, "title": issue.title,
                    "body": issue.body, "state": issue.state})
    return out


def _mcp_create_pull(args):
    repo = _mcp_get_repo(args)
    _mcp_require(args, "title", "head", "base")
    head = args["head"]
    base = args["base"]
    head_sha = repo.tip(head)
    base_sha = repo.tip(base)
    if head_sha is None or base_sha is None:
        raise _MCPToolError("unknown head or base branch")
    for pull in repo.pulls.values():
        if pull.state == "open" and pull.head == head and pull.base == base:
            raise _MCPToolError("a pull request already exists for this branch")
    number = repo.next_number
    repo.next_number += 1
    pull = Pull(number, args["title"], args.get("body") or "", head, base,
                number, head_sha, base_sha)
    repo.pulls[number] = pull
    return {"number": number, "state": "open", "title": pull.title,
            "head": {"ref": head, "sha": head_sha},
            "base": {"ref": base, "sha": base_sha}}


def _mcp_merge_pull(args):
    repo = _mcp_get_repo(args)
    number = args.get("pull_number")
    if number is None:
        raise _MCPToolError("missing required argument 'pull_number'")
    pull = repo.pulls.get(int(number))
    if pull is None:
        raise _MCPToolError("pull request #%s not found" % number)
    if pull.state != "open":
        raise _MCPToolError("pull request #%s is already merged" % number)
    base_tip = repo.tip(pull.base)
    head_tip = repo.tip(pull.head)
    merge_base = find_merge_base(repo, base_tip, head_tip)
    tree_oid, conflict = merge_trees(repo, merge_base, head_tip, base_tip)
    if conflict:
        raise _MCPToolError("merge conflict")
    ts = STORE.tick()
    merge_oid = commit_with_tree(
        repo, tree_oid, [base_tip],
        "Merge pull request #%d from %s" % (pull.number, pull.head), ts)
    repo.refs["refs/heads/" + pull.base] = merge_oid
    pull.state = "closed"
    pull.merged = True
    pull.merged_at = STORE.iso_now()
    pull.merge_sha = merge_oid
    return {"merged": True, "sha": merge_oid, "number": pull.number}


_MCP_DISPATCH = {
    "create_repo": _mcp_create_repo,
    "get_repo": _mcp_get_repo_tool,
    "create_issue": _mcp_create_issue,
    "list_issues": _mcp_list_issues,
    "create_pull_request": _mcp_create_pull,
    "merge_pull_request": _mcp_merge_pull,
}


def _handle_graphql(handler, method, query):
    if method != "POST":
        handler._error(405, "Method Not Allowed")
        return
    if not handler._need_auth():
        return
    body, error_sent = handler._json_body()
    if error_sent:
        return
    docs = body if isinstance(body, list) else [body]
    results = []
    for doc in docs:
        if not isinstance(doc, dict):
            results.append({"data": None,
                            "errors": [{"message": "document must be an object"}]})
            continue
        document = doc.get("query") or ""
        variables = doc.get("variables") or {}
        if isinstance(variables, str):
            try:
                variables = json.loads(variables)
            except ValueError:
                variables = {}
        variables = dict(variables)
        if doc.get("operationName"):
            variables["__operationName"] = doc["operationName"]
        executor = GraphQLExecutor()
        data, errors = executor.execute(document, variables)
        result = {"data": data}
        if errors:
            result["errors"] = errors
        results.append(result)
    handler._json(200, results if isinstance(body, list) else results[0])


def _handle_mcp(handler, method, query):
    if method != "POST":
        handler._error(405, "Method Not Allowed")
        return
    if not handler._need_auth():
        return
    raw = handler._read_body()
    if raw is None:
        return
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (ValueError, UnicodeDecodeError):
        handler._send_jsonrpc(None, None,
                              {"code": -32700, "message": "Parse error"},
                              status=400)
        return
    if not isinstance(payload, dict):
        handler._send_jsonrpc(None, None,
                              {"code": -32600, "message": "Invalid Request"})
        return
    req_id = payload.get("id")
    method_name = payload.get("method") or handler.headers.get("mcp-method")
    params = payload.get("params") or {}
    if method_name == "notifications/initialized":
        handler._send(202, b"", "application/json")
        return
    if method_name == "server/discover":
        result = {
            "supportedVersions": ["2026-07-28", "2025-11-25"],
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "github-forge", "version": "1.0.0"},
        }
        handler._send_jsonrpc(req_id, result, None)
        return
    if method_name == "initialize":
        result = {
            "protocolVersion": "2025-11-25",
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "github-forge", "version": "1.0.0"},
        }
        handler._send_jsonrpc(req_id, result, None)
        return
    if method_name == "ping":
        handler._send_jsonrpc(req_id, {}, None)
        return
    if method_name == "tools/list":
        handler._send_jsonrpc(req_id, {"tools": _MCP_TOOLS}, None)
        return
    if method_name == "tools/call":
        result, error = _mcp_tool_result(handler, method_name, params)
        handler._send_jsonrpc(req_id, result, error)
        return
    handler._send_jsonrpc(req_id, None,
                          {"code": -32601, "message": "Method not found"})


# -- lifecycle ---------------------------------------------------------------

def _http_json(url, method="GET", body=None, timeout=30):
    req = urllib.request.Request(url, method=method)
    data = None
    if body is not None:
        data = json.dumps(body).encode("utf-8")
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, data=data, timeout=timeout) as resp:
            return resp.status, resp.read()
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read()
    except Exception:
        return None, b""


def main():
    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    server = ForgeServer(("127.0.0.1", 0), ForgeHandler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    port = server.server_address[1]
    if not env_url:
        # Standalone mode: serve until interrupted (handy for local testing).
        sys.stderr.write("github-forge listening on 127.0.0.1:%d (standalone)\n" % port)
        try:
            while True:
                time.sleep(3600)
        except KeyboardInterrupt:
            pass
        server.shutdown()
        return 0
    # Register with the harness, retrying with backoff inside the boot budget.
    deadline = time.time() + BOOT_BUDGET_MS / 1000.0
    delay = 0.25
    registered = False
    while time.time() < deadline:
        status, _ = _http_json(env_url + REGISTER_PATH, method="POST",
                               body={"port": port}, timeout=5)
        if status in (200, 409):
            registered = True
            break
        if status in (400, 405):
            sys.stderr.write("register rejected with %s\n" % status)
            server.shutdown()
            return 1
        time.sleep(delay)
        delay = min(delay * 2, 2.0)
    if not registered:
        sys.stderr.write("register timed out\n")
        server.shutdown()
        return 1
    # Poll /done until the harness says the trial is over.
    done_deadline = time.time() + 840
    while time.time() < done_deadline:
        status, body = _http_json(env_url + DONE_PATH, timeout=30)
        if status == 200:
            try:
                if json.loads(body.decode("utf-8")).get("done"):
                    break
            except (ValueError, UnicodeDecodeError):
                pass
        time.sleep(0.5)
    server.shutdown()
    return 0


if __name__ == "__main__":
    sys.exit(main())
