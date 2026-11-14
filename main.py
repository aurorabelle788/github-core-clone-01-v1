#!/usr/bin/env python3
"""github-core-clone-01 entry: a standalone GitHub-compatible git forge.

One process, stdlib only (Python 3.13). Serves git smart HTTP (protocol
v2 and v0), the REST v3 API, GraphQL v4 and MCP from an in-memory store.
No UI, no outside service, no git binary, no wall clock and no unseeded
randomness in anything the server creates: every server-made commit and
timestamp is fixed, so a replay leaves identical state.

Lifecycle: bind an ephemeral port, POST {"port": N} to
$MAKEFUN_ENV_URL/register, then long-poll GET $MAKEFUN_ENV_URL/done
until {"done": true} and exit 0. GET /healthz answers {"ok": true}.
Bearer token is $MAKEFUN_SHOP_TOKEN (when set, every API/git surface
requires it; /healthz is exempt).
"""
import base64
import difflib
import hashlib
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.request
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

VIEWER = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"
STRANGER = "olgabauer"
FIXED_TS = 1700000000
FIXED_ISO = "2024-01-15T00:00:00Z"
ZERO_OID = "0" * 40
AGENT = "forge/1.0"
TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "")

# ---------------------------------------------------------------- git objects

def sha1(b):
    return hashlib.sha1(b).hexdigest()


def obj_hash(typ, data):
    return sha1(("%s %d\0" % (typ, len(data))).encode() + data)


def encode_tree(entries):
    """entries: list of (mode, name, oid). Sorted by git's rule (a directory
    sorts as name + '/')."""
    def key(e):
        mode, name, oid = e
        return name + ("/" if mode == "40000" else "")
    out = bytearray()
    for mode, name, oid in sorted(entries, key=key):
        out += ("%s %s\0" % (mode, name)).encode() + bytes.fromhex(oid)
    return bytes(out)


def parse_tree(data):
    entries = []
    i = 0
    while i < len(data):
        sp = data.index(b" ", i)
        mode = data[i:sp].decode()
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul].decode()
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        i = nul + 21
    return entries


def build_commit(tree_oid, parents, message, author=None, ts=FIXED_TS):
    if author is None:
        author = "%s <%s>" % (VIEWER_NAME, VIEWER_EMAIL)
    lines = ["tree %s" % tree_oid]
    for p in parents:
        lines.append("parent %s" % p)
    lines.append("author %s %d +0000" % (author, ts))
    lines.append("committer %s %d +0000" % (author, ts))
    lines.append("")
    lines.append(message)
    return ("\n".join(lines) + "\n").encode()


def parse_commit(data):
    head, _, msg = data.partition(b"\n\n")
    tree = None
    parents = []
    for line in head.decode().split("\n"):
        if line.startswith("tree "):
            tree = line[5:]
        elif line.startswith("parent "):
            parents.append(line[7:])
    return {"tree": tree, "parents": parents, "message": msg.decode().rstrip("\n")}


def build_tag(obj, typ, tag, message, tagger=None, ts=FIXED_TS):
    if tagger is None:
        tagger = "%s <%s>" % (VIEWER_NAME, VIEWER_EMAIL)
    text = ("object %s\ntype %s\ntag %s\ntagger %s %d +0000\n\n%s\n"
            % (obj, typ, tag, tagger, ts, message))
    return text.encode()


def parse_tag(data):
    head, _, msg = data.partition(b"\n\n")
    obj = None
    typ = None
    for line in head.decode().split("\n"):
        if line.startswith("object "):
            obj = line[7:]
        elif line.startswith("type "):
            typ = line[5:]
    return {"object": obj, "type": typ, "message": msg.decode()}


# ---------------------------------------------------------------- packfiles

def _read_varint(data, pos):
    """Pack object header varint: first byte holds 4 size bits + 3 type bits."""
    b = data[pos]
    pos += 1
    tnum = (b >> 4) & 0x07
    size = b & 0x0F
    shift = 4
    while b & 0x80:
        b = data[pos]
        pos += 1
        size |= (b & 0x7F) << shift
        shift += 7
    return tnum, size, pos


def _read_ofs_delta(data, pos):
    b = data[pos]
    pos += 1
    off = b & 0x7F
    while b & 0x80:
        b = data[pos]
        pos += 1
        off = ((off + 1) << 7) | (b & 0x7F)
    return off, pos


def _read_delta_varint(data, pos):
    result = 0
    shift = 0
    while True:
        b = data[pos]
        pos += 1
        result |= (b & 0x7F) << shift
        shift += 7
        if not (b & 0x80):
            break
    return result, pos


def apply_delta(base, delta):
    src_size, pos = _read_delta_varint(delta, 0)
    dst_size, pos = _read_delta_varint(delta, pos)
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            if op & 0x01:
                cp_off = delta[pos]; pos += 1
            if op & 0x02:
                cp_off |= delta[pos] << 8; pos += 1
            if op & 0x04:
                cp_off |= delta[pos] << 16; pos += 1
            if op & 0x08:
                cp_off |= delta[pos] << 24; pos += 1
            if op & 0x10:
                cp_size = delta[pos]; pos += 1
            if op & 0x20:
                cp_size |= delta[pos] << 8; pos += 1
            if op & 0x40:
                cp_size |= delta[pos] << 16; pos += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != dst_size:
        raise ValueError("delta output size mismatch")
    return bytes(out)


_TYPE_NUM = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
_NUM_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def write_pack(objects):
    """objects: list of (type, data). Non-delta pack, version 2, SHA-1 trailer."""
    out = bytearray(b"PACK")
    out += (2).to_bytes(4, "big")
    out += len(objects).to_bytes(4, "big")
    for typ, data in objects:
        tnum = _TYPE_NUM[typ]
        size = len(data)
        b0 = (size & 0x0F) | (tnum << 4)
        size >>= 4
        hdr = bytearray()
        if size:
            hdr.append(b0 | 0x80)
            while size:
                b = size & 0x7F
                size >>= 7
                hdr.append(b | 0x80 if size else b)
        else:
            hdr.append(b0)
        out += hdr
        out += zlib.compress(data, 6)
    out += hashlib.sha1(bytes(out)).digest()
    return bytes(out)


def read_pack(data, resolve_base=None):
    """Parse a packfile. Returns dict oid -> (type, data). resolve_base(oid)
    looks up a base object outside the pack (thin packs). Raises ValueError
    on a bad magic, version, trailer or unresolvable delta."""
    if len(data) < 32 or data[:4] != b"PACK":
        raise ValueError("bad pack magic")
    version = int.from_bytes(data[4:8], "big")
    if version not in (2, 3):
        raise ValueError("bad pack version")
    if hashlib.sha1(data[:-20]).digest() != data[-20:]:
        raise ValueError("bad pack trailer")
    count = int.from_bytes(data[8:12], "big")
    pos = 12
    raw = []  # (offset, tnum, base_ref, delta_bytes, size)
    for _ in range(count):
        start = pos
        tnum, size, pos = _read_varint(data, pos)
        if tnum == 6:
            off, pos = _read_ofs_delta(data, pos)
            base_ref = ("ofs", start - off)
        elif tnum == 7:
            base_ref = ("ref", data[pos:pos + 20].hex())
            pos += 20
        elif tnum in _NUM_TYPE:
            base_ref = None
        else:
            raise ValueError("bad pack entry type %d" % tnum)
        dec = zlib.decompressobj()
        chunk = dec.decompress(data[pos:])
        pos += len(data[pos:]) - len(dec.unused_data)
        raw.append((start, tnum, base_ref, chunk, size))
    by_offset = {}
    resolved = {}

    def resolve_entry(idx):
        start, tnum, base_ref, chunk, size = raw[idx]
        if start in resolved:
            return resolved[start]
        if tnum in _NUM_TYPE:
            typ = _NUM_TYPE[tnum]
            if len(chunk) != size:
                raise ValueError("pack object size mismatch")
            result = (typ, chunk)
        else:
            if base_ref[0] == "ofs":
                base_off = base_ref[1]
                base = by_offset.get(base_off)
                if base is None:
                    raise ValueError("delta base offset not in pack")
                btyp, bdata = base
            else:
                boid = base_ref[1]
                base = None
                for (o, t, d) in resolved.values():
                    if o == boid:
                        base = (t, d)
                        break
                if base is None and resolve_base is not None:
                    base = resolve_base(boid)
                if base is None:
                    raise ValueError("delta base %s not found" % boid)
                btyp, bdata = base
            result = (btyp, apply_delta(bdata, chunk))
        oid = obj_hash(result[0], result[1])
        resolved[start] = (oid, result[0], result[1])
        by_offset[start] = result
        return resolved[start]

    out = {}
    for i in range(len(raw)):
        oid, typ, data = resolve_entry(i)
        out[oid] = (typ, data)
    return out


# ---------------------------------------------------------------- pkt-lines

def pkt(payload):
    if isinstance(payload, str):
        payload = payload.encode()
    return ("%04x" % (len(payload) + 4)).encode() + payload


FLUSH = b"0000"
DELIM = b"0001"


def parse_pkt_lines(data):
    """Returns (packets, rest_offset). Each packet is ('data', bytes),
    ('flush', None) or ('delim', None). Raises ValueError on truncation."""
    packets = []
    pos = 0
    while pos < len(data):
        if pos + 4 > len(data):
            raise ValueError("truncated pkt-line header")
        try:
            ln = int(data[pos:pos + 4], 16)
        except ValueError:
            raise ValueError("bad pkt-line length")
        if ln == 0:
            packets.append(("flush", None))
            pos += 4
        elif ln == 1:
            packets.append(("delim", None))
            pos += 4
        elif ln == 2:
            raise ValueError("bad pkt-line length 2")
        else:
            if pos + ln > len(data):
                raise ValueError("truncated pkt-line")
            packets.append(("data", data[pos + 4:pos + ln]))
            pos += ln
    return packets, pos


def sideband_pack(pack_bytes, band=1):
    """Wrap pack bytes in sideband band-1 pkt-lines (<= 65515 payload bytes
    of pack data per packet, the pkt-line cap less the band byte)."""
    out = bytearray()
    step = 65515
    for i in range(0, len(pack_bytes), step):
        chunk = pack_bytes[i:i + step]
        out += pkt(bytes([band]) + chunk)
    return bytes(out)

# ---------------------------------------------------------------- the store

STORE_LOCK = threading.RLock()
REPOS = {}  # (owner, name) -> Repo
NEXT_REPO_ID = [10000]
NEXT_ISSUE_ID = [200000]
NEXT_COMMENT_ID = [300000]
NEXT_LABEL_ID = [400000]
NEXT_REQ_ID = [0]


def _next(counter):
    v = counter[0]
    counter[0] += 1
    return v


def gid(kind, *parts):
    raw = ":".join([kind] + [str(p) for p in parts])
    return base64.urlsafe_b64encode(raw.encode()).decode().rstrip("=")


def ungid(value):
    try:
        padded = value + "=" * (-len(value) % 4)
        return base64.urlsafe_b64decode(padded).decode()
    except Exception:
        return None


class Repo:
    def __init__(self, name, owner=VIEWER, description="", private=False):
        self.id = _next(NEXT_REPO_ID)
        self.name = name
        self.owner = owner
        self.description = description or ""
        self.private = bool(private)
        self.default_branch = "main"
        self.objects = {}   # oid -> (type, data)
        self.refs = {}      # 'refs/heads/main' -> oid
        self.labels = {}    # name -> label dict
        self.issues = {}    # number -> issue dict
        self.pulls = {}     # number -> pr dict
        self.comments = {}  # issue number -> [comment dict]
        self.next_number = 1
        self.seq = 0
        self.next_comment_id = 1
        self.fetch_cache = {}  # (wants, depth, haves, shallow) -> (pack, shallow, unshallow)

    # -- objects ------------------------------------------------------
    def put_obj(self, typ, data):
        oid = obj_hash(typ, data)
        self.objects[oid] = (typ, data)
        return oid

    def get_obj(self, oid):
        return self.objects.get(oid)

    def has_obj(self, oid):
        return oid in self.objects

    def resolve(self, oid):
        """Follow tags to the object they point at. Returns (oid, type, data)."""
        cur = oid
        for _ in range(10):
            ent = self.objects.get(cur)
            if ent is None:
                return None
            typ, data = ent
            if typ == "tag":
                cur = parse_tag(data)["object"]
                continue
            return (cur, typ, data)
        return None

    def commit_of(self, oid):
        """Resolve oid (commit or tag) to a commit oid, or None."""
        r = self.resolve(oid)
        if r is None or r[1] != "commit":
            return None
        return r[0]

    # -- refs ---------------------------------------------------------
    def ref_tip(self, refname):
        return self.refs.get(refname)

    def default_tip(self):
        return self.refs.get("refs/heads/" + self.default_branch)

    def invalidate_cache(self):
        self.fetch_cache = {}


def get_repo(owner, name):
    return REPOS.get((owner, name))


def create_repo_obj(name, owner=VIEWER, description="", private=False):
    repo = Repo(name, owner=owner, description=description, private=private)
    REPOS[(owner, name)] = repo
    return repo


# -- tree / file helpers ----------------------------------------------

def commit_tree(repo, commit_oid):
    r = repo.resolve(commit_oid)
    if r is None or r[1] != "commit":
        return None
    return parse_commit(r[2])["tree"]


def commit_parents(repo, commit_oid):
    r = repo.resolve(commit_oid)
    if r is None or r[1] != "commit":
        return []
    return parse_commit(r[2])["parents"]


def commit_message(repo, commit_oid):
    r = repo.resolve(commit_oid)
    if r is None or r[1] != "commit":
        return ""
    return parse_commit(r[2])["message"]


def ancestors(repo, start):
    """All commit oids reachable from start (start may be a tag)."""
    seen = set()
    stack = []
    c = repo.commit_of(start)
    if c:
        stack.append(c)
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(commit_parents(repo, cur))
    return seen


def is_ancestor(repo, anc, desc):
    a = repo.commit_of(anc)
    d = repo.commit_of(desc)
    if a is None or d is None:
        return False
    if a == d:
        return True
    seen = set()
    stack = [d]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        for p in commit_parents(repo, cur):
            if p == a:
                return True
            stack.append(p)
    return False


def merge_base(repo, a, b):
    """First common ancestor (linear histories: exact)."""
    a_c = repo.commit_of(a)
    b_c = repo.commit_of(b)
    if a_c is None or b_c is None:
        return None
    b_anc = ancestors(repo, b_c)
    # BFS from a, nearest first.
    seen = set()
    queue = [a_c]
    while queue:
        cur = queue.pop(0)
        if cur in seen:
            continue
        seen.add(cur)
        if cur in b_anc:
            return cur
        queue.extend(commit_parents(repo, cur))
    return None


def tree_get(repo, tree_oid, path):
    """Returns (type, oid) for path in tree, or None. type is 'blob'/'tree'."""
    if tree_oid is None:
        return None
    parts = [p for p in path.split("/") if p != ""]
    cur = tree_oid
    for i, part in enumerate(parts):
        ent = repo.get_obj(cur)
        if ent is None or ent[0] != "tree":
            return None
        found = None
        for mode, name, oid in parse_tree(ent[1]):
            if name == part:
                found = (mode, oid)
                break
        if found is None:
            return None
        mode, oid = found
        if i == len(parts) - 1:
            return ("tree" if mode == "40000" else "blob", oid)
        if mode != "40000":
            return None
        cur = oid
    return ("tree", tree_oid)


def tree_list(repo, tree_oid, path):
    """Immediate children of the directory at path. Returns list of
    (mode, name, oid, type) or None when the path is not a directory."""
    if tree_oid is None:
        return None
    if path in ("", "/"):
        ent = repo.get_obj(tree_oid)
        if ent is None or ent[0] != "tree":
            return None
        return [(m, n, o, "tree" if m == "40000" else "blob")
                for (m, n, o) in parse_tree(ent[1])]
    got = tree_get(repo, tree_oid, path)
    if got is None or got[0] != "tree":
        return None
    ent = repo.get_obj(got[1])
    if ent is None:
        return None
    return [(m, n, o, "tree" if m == "40000" else "blob")
            for (m, n, o) in parse_tree(ent[1])]


def tree_set(repo, base_tree_oid, path, blob_oid):
    """Return the oid of a new tree equal to base_tree with path set to
    blob_oid (or removed when blob_oid is None). Stores new tree objects."""
    parts = [p for p in path.split("/") if p != ""]
    if not parts:
        return base_tree_oid

    def build(tree_oid, idx):
        entries = {}
        if tree_oid is not None:
            ent = repo.get_obj(tree_oid)
            if ent is not None and ent[0] == "tree":
                for mode, name, oid in parse_tree(ent[1]):
                    entries[name] = (mode, oid)
        name = parts[idx]
        if idx == len(parts) - 1:
            if blob_oid is None:
                entries.pop(name, None)
            else:
                entries[name] = ("100644", blob_oid)
        else:
            sub = entries.get(name)
            sub_tree = sub[1] if sub is not None and sub[0] == "40000" else None
            new_sub = build(sub_tree, idx + 1)
            if new_sub is None:
                entries.pop(name, None)
            else:
                entries[name] = ("40000", new_sub)
        if not entries:
            return None
        data = encode_tree([(m, n, o) for n, (m, o) in entries.items()])
        return repo.put_obj("tree", data)

    return build(base_tree_oid, 0)


def make_commit(repo, tree_oid, parents, message):
    data = build_commit(tree_oid, parents, message)
    return repo.put_obj("commit", data)


def diff_trees(repo, base_tree, head_tree):
    """Recursive diff. Returns list of (path, status, old_blob, new_blob)
    with status in added/removed/modified, sorted by path."""
    def flat(tree_oid, prefix, out):
        if tree_oid is None:
            return
        ent = repo.get_obj(tree_oid)
        if ent is None or ent[0] != "tree":
            return
        for mode, name, oid in parse_tree(ent[1]):
            p = prefix + name
            if mode == "40000":
                flat(oid, p + "/", out)
            else:
                out[p] = oid

    base_files = {}
    head_files = {}
    flat(base_tree, "", base_files)
    flat(head_tree, "", head_files)
    out = []
    for path in sorted(set(base_files) | set(head_files)):
        if path not in base_files:
            out.append((path, "added", None, head_files[path]))
        elif path not in head_files:
            out.append((path, "removed", base_files[path], None))
        elif base_files[path] != head_files[path]:
            out.append((path, "modified", base_files[path], head_files[path]))
    return out


def line_counts(repo, old_oid, new_oid):
    def lines(oid):
        if oid is None:
            return []
        ent = repo.get_obj(oid)
        if ent is None:
            return []
        return ent[1].decode("utf-8", "replace").splitlines()
    a = lines(old_oid)
    b = lines(new_oid)
    sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)
    add = 0
    dele = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag in ("insert", "replace"):
            add += j2 - j1
        if tag in ("delete", "replace"):
            dele += i2 - i1
    return add, dele


def pr_diff(repo, pr):
    """Diff between the PR base tip tree and head tip tree."""
    base_tip = repo.ref_tip("refs/heads/" + pr["base"]["ref"])
    head_tip = repo.ref_tip("refs/heads/" + pr["head"]["ref"])
    base_tree = commit_tree(repo, base_tip) if base_tip else None
    head_tree = commit_tree(repo, head_tip) if head_tip else None
    return diff_trees(repo, base_tree, head_tree)


def pr_conflicts(repo, pr):
    """Paths changed on both sides of the merge-base with different results
    (or changed on one side and deleted on the other). Returns the list."""
    base_tip = repo.ref_tip("refs/heads/" + pr["base"]["ref"])
    head_tip = repo.ref_tip("refs/heads/" + pr["head"]["ref"])
    if base_tip is None or head_tip is None:
        return []
    mb = merge_base(repo, head_tip, base_tip)
    if mb is None:
        return []
    mb_tree = commit_tree(repo, mb)
    base_tree = commit_tree(repo, base_tip)
    head_tree = commit_tree(repo, head_tip)
    head_changes = {p: (s, nb) for (p, s, ob, nb) in diff_trees(repo, mb_tree, head_tree)}
    base_changes = {p: (s, nb) for (p, s, ob, nb) in diff_trees(repo, mb_tree, base_tree)}
    conflicts = []
    for path in sorted(set(head_changes) & set(base_changes)):
        hs, hblob = head_changes[path]
        bs, bblob = base_changes[path]
        if hs == "removed" or bs == "removed":
            conflicts.append(path)
        elif hblob != bblob:
            conflicts.append(path)
    return conflicts


# -- issues / pulls / labels / comments -------------------------------

def create_issue_obj(repo, title, body="", labels=None):
    repo.seq += 1
    number = repo.next_number
    repo.next_number += 1
    issue = {
        "id": _next(NEXT_ISSUE_ID),
        "number": number,
        "title": title or "",
        "body": body or "",
        "state": "open",
        "labels": list(labels or []),
        "user": {"login": VIEWER, "id": VIEWER_ID},
        "created_at": FIXED_ISO,
        "updated_at": FIXED_ISO,
        "closed_at": None,
        "seq": repo.seq,
    }
    repo.issues[number] = issue
    repo.comments[number] = []
    return issue


def create_pr_obj(repo, title, body, head, base):
    head_tip = repo.ref_tip("refs/heads/" + head)
    base_tip = repo.ref_tip("refs/heads/" + base)
    if head_tip is None or base_tip is None:
        return None
    repo.seq += 1
    number = repo.next_number
    repo.next_number += 1
    pr = {
        "id": _next(NEXT_ISSUE_ID),
        "number": number,
        "title": title or "",
        "body": body or "",
        "state": "open",
        "head": {"ref": head, "sha": repo.commit_of(head_tip) or head_tip,
                 "label": "%s:%s" % (VIEWER, head)},
        "base": {"ref": base, "sha": repo.commit_of(base_tip) or base_tip,
                 "label": "%s:%s" % (VIEWER, base)},
        "merged": False,
        "merged_at": None,
        "merge_commit_sha": None,
        "user": {"login": VIEWER, "id": VIEWER_ID},
        "created_at": FIXED_ISO,
        "updated_at": FIXED_ISO,
        "closed_at": None,
        "seq": repo.seq,
    }
    repo.pulls[number] = pr
    return pr


def merge_pr_obj(repo, pr):
    """Squash-merge the PR onto its base branch. Returns (status, payload):
    status 200 on success, 405 on conflict, 404 when the PR is unknown."""
    if pr["state"] != "open":
        return (405, {"message": "Pull request is already closed"})
    conflicts = pr_conflicts(repo, pr)
    if conflicts:
        return (405, {"message": "Merge conflict: %s" % ", ".join(conflicts)})
    base_tip = repo.ref_tip("refs/heads/" + pr["base"]["ref"])
    head_tip = repo.ref_tip("refs/heads/" + pr["head"]["ref"])
    mb = merge_base(repo, head_tip, base_tip)
    mb_tree = commit_tree(repo, mb) if mb else None
    base_tree = commit_tree(repo, base_tip) if base_tip else None
    head_tree = commit_tree(repo, head_tip) if head_tip else None
    new_tree = base_tree
    for path, status, _old, new_blob in diff_trees(repo, mb_tree, head_tree):
        new_tree = tree_set(repo, new_tree, path, new_blob)
    if new_tree is None:
        new_tree = repo.put_obj("tree", encode_tree([]))
    parents = [base_tip] if base_tip else []
    msg = "Merge pull request #%d from %s/%s" % (
        pr["number"], VIEWER, pr["head"]["ref"])
    merge_commit = make_commit(repo, new_tree, parents, msg)
    repo.refs["refs/heads/" + pr["base"]["ref"]] = merge_commit
    pr["state"] = "closed"
    pr["merged"] = True
    pr["merged_at"] = FIXED_ISO
    pr["merge_commit_sha"] = merge_commit
    pr["closed_at"] = FIXED_ISO
    repo.invalidate_cache()
    return (200, {"sha": merge_commit, "merged": True, "message": msg})


def create_comment_obj(repo, number, body):
    cid = repo.next_comment_id
    repo.next_comment_id += 1
    comment = {
        "id": _next(NEXT_COMMENT_ID),
        "body": body or "",
        "user": {"login": VIEWER, "id": VIEWER_ID},
        "created_at": FIXED_ISO,
        "updated_at": FIXED_ISO,
    }
    repo.comments.setdefault(number, []).append(comment)
    return comment


# -- REST serializers ---------------------------------------------------

def repo_json(repo):
    return {
        "id": repo.id,
        "node_id": gid("Repository", repo.id),
        "name": repo.name,
        "full_name": "%s/%s" % (repo.owner, repo.name),
        "owner": {"login": repo.owner, "id": VIEWER_ID, "type": "User",
                  "node_id": gid("User", VIEWER_ID)},
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "created_at": FIXED_ISO,
        "updated_at": FIXED_ISO,
        "pushed_at": FIXED_ISO,
        "html_url": "https://example.invalid/%s/%s" % (repo.owner, repo.name),
        "url": "https://example.invalid/api/v3/repos/%s/%s" % (repo.owner, repo.name),
        "clone_url": "https://example.invalid/%s/%s.git" % (repo.owner, repo.name),
        "git_url": "git://example.invalid/%s/%s.git" % (repo.owner, repo.name),
        "ssh_url": "git@example.invalid:%s/%s.git" % (repo.owner, repo.name),
        "has_issues": True,
        "has_projects": True,
        "has_wiki": True,
        "has_pages": False,
        "has_downloads": True,
        "forks_count": 0,
        "stargazers_count": 0,
        "watchers_count": 0,
        "open_issues_count": len([i for i in repo.issues.values()
                                  if i["state"] == "open"]),
        "license": None,
        "topics": [],
        "visibility": "private" if repo.private else "public",
        "archived": False,
        "disabled": False,
        "fork": False,
        "size": 0,
        "language": None,
    }


def issue_json(repo, issue):
    labels = []
    for name in issue["labels"]:
        lab = repo.labels.get(name)
        labels.append({"id": lab["id"] if lab else 0,
                       "node_id": gid("Label", repo.id, name),
                       "name": name,
                       "color": lab["color"] if lab else "ededed",
                       "description": lab["description"] if lab else "",
                       "default": False,
                       "url": ""})
    return {
        "id": issue["id"],
        "node_id": gid("Issue", repo.id, issue["number"]),
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "user": issue["user"],
        "labels": labels,
        "assignee": None,
        "assignees": [],
        "milestone": None,
        "comments": len(repo.comments.get(issue["number"], [])),
        "created_at": issue["created_at"],
        "updated_at": issue["updated_at"],
        "closed_at": issue["closed_at"],
        "html_url": "https://example.invalid/%s/%s/issues/%d"
                    % (repo.owner, repo.name, issue["number"]),
        "url": "https://example.invalid/api/v3/repos/%s/%s/issues/%d"
               % (repo.owner, repo.name, issue["number"]),
    }


def pr_json(repo, pr):
    return {
        "id": pr["id"],
        "node_id": gid("PullRequest", repo.id, pr["number"]),
        "number": pr["number"],
        "title": pr["title"],
        "body": pr["body"],
        "state": pr["state"],
        "user": pr["user"],
        "head": {"label": pr["head"]["label"], "ref": pr["head"]["ref"],
                 "sha": pr["head"]["sha"],
                 "user": {"login": VIEWER, "id": VIEWER_ID},
                 "repo": repo_json(repo)},
        "base": {"label": pr["base"]["label"], "ref": pr["base"]["ref"],
                 "sha": pr["base"]["sha"],
                 "user": {"login": VIEWER, "id": VIEWER_ID},
                 "repo": repo_json(repo)},
        "merged": pr["merged"],
        "merged_at": pr["merged_at"],
        "merge_commit_sha": pr["merge_commit_sha"],
        "mergeable": len(pr_conflicts(repo, pr)) == 0 if pr["state"] == "open" else None,
        "mergeable_state": "clean" if pr["state"] == "open" and not pr_conflicts(repo, pr) else "dirty",
        "created_at": pr["created_at"],
        "updated_at": pr["updated_at"],
        "closed_at": pr["closed_at"],
        "html_url": "https://example.invalid/%s/%s/pull/%d"
                    % (repo.owner, repo.name, pr["number"]),
        "url": "https://example.invalid/api/v3/repos/%s/%s/pulls/%d"
               % (repo.owner, repo.name, pr["number"]),
    }


def comment_json(repo, comment):
    return {
        "id": comment["id"],
        "node_id": gid("IssueComment", repo.id, comment["id"]),
        "body": comment["body"],
        "user": comment["user"],
        "created_at": comment["created_at"],
        "updated_at": comment["updated_at"],
        "html_url": "https://example.invalid/%s/%s/issues/comments/%d"
                    % (repo.owner, repo.name, comment["id"]),
        "url": "https://example.invalid/api/v3/repos/%s/%s/issues/comments/%d"
               % (repo.owner, repo.name, comment["id"]),
    }


def branch_json(repo, refname):
    tip = repo.refs.get(refname)
    name = refname[len("refs/heads/"):]
    commit = {"sha": tip or ZERO_OID, "url": ""}
    if tip:
        r = repo.resolve(tip)
        if r is not None and r[1] == "commit":
            commit["message"] = parse_commit(r[2])["message"]
    return {"name": name, "commit": commit, "protected": False}

# ---------------------------------------------------------------- git protocol

def adv_v2(repo):
    caps = ["version 2", "ls-refs=unborn", "fetch=shallow wait-for-done",
            "agent=%s" % AGENT, "object-format=sha1"]
    out = b"".join(pkt(c + "\n") for c in caps)
    return out + FLUSH


def adv_v0(repo, service):
    if service == "git-upload-pack":
        caps = ["side-band-64k", "shallow", "thin-pack", "ofs-delta",
                "multi_ack", "symref=HEAD:refs/heads/%s" % repo.default_branch,
                "agent=%s" % AGENT]
    else:
        caps = ["report-status", "side-band-64k", "delete-refs", "ofs-delta",
                "agent=%s" % AGENT]
    out = bytearray()
    out += pkt("# service=%s\n" % service)
    out += FLUSH
    refs = sorted(repo.refs.items())
    if not refs:
        out += pkt("%s capabilities^{}\0%s\n" % (ZERO_OID, " ".join(caps)))
        out += FLUSH
        return bytes(out)
    head_oid = repo.default_tip() or ZERO_OID
    out += pkt("%s HEAD\0%s\n" % (head_oid, " ".join(caps)))
    for refname, oid in refs:
        out += pkt("%s %s\n" % (oid, refname))
    out += FLUSH
    return bytes(out)


def ls_refs_body(repo, prefixes, peel, symrefs, unborn):
    def matches(name):
        if not prefixes:
            return True
        return any(name.startswith(p) for p in prefixes)

    out = bytearray()
    default_tip = repo.default_tip()
    if matches("HEAD"):
        if default_tip is None:
            if unborn:
                out += pkt("unborn HEAD symref-target:refs/heads/%s\n"
                           % repo.default_branch)
        else:
            line = "%s HEAD" % default_tip
            if symrefs:
                line += " symref-target:refs/heads/%s" % repo.default_branch
            out += pkt(line + "\n")
    for refname in sorted(repo.refs):
        if not matches(refname):
            continue
        oid = repo.refs[refname]
        line = "%s %s" % (oid, refname)
        if peel:
            ent = repo.get_obj(oid)
            if ent is not None and ent[0] == "tag":
                target = parse_tag(ent[1])["object"]
                c = repo.commit_of(target)
                if c:
                    line += " peeled:%s" % c
        out += pkt(line + "\n")
    out += FLUSH
    return bytes(out)


def _held_set(repo, haves, shallow_set):
    """Objects the client already holds: everything reachable from the haves,
    except that a shallow boundary commit's parents are NOT held (a shallow
    clone has the boundary commit but not its history). Returns
    (held_objects, held_commits)."""
    held = set()
    held_commits = set()
    stack = []
    for h in haves:
        c = repo.commit_of(h)
        stack.append(c if c is not None else h)
    while stack:
        oid = stack.pop()
        if oid in held:
            continue
        ent = repo.get_obj(oid)
        if ent is None:
            continue
        held.add(oid)
        if ent[0] == "commit":
            held_commits.add(oid)
            tree = parse_commit(ent[1])["tree"]
            if tree:
                stack.append(tree)
            if oid not in shallow_set:
                stack.extend(parse_commit(ent[1])["parents"])
        elif ent[0] == "tree":
            for _m, _n, sub in parse_tree(ent[1]):
                stack.append(sub)
        elif ent[0] == "tag":
            stack.append(parse_tag(ent[1])["object"])
    return held, held_commits


def compute_fetch(repo, wants, haves, depth, shallow):
    """Returns (pack_bytes, shallow_list, unshallow_list)."""
    cache_key = (tuple(sorted(wants)), tuple(sorted(haves)), depth,
                 tuple(sorted(shallow)))
    cached = repo.fetch_cache.get(cache_key)
    if cached is not None:
        return cached
    # BFS distances from the wants.
    dist = {}
    queue = []
    for w in wants:
        c = repo.commit_of(w)
        if c is not None and c not in dist:
            dist[c] = 0
            queue.append(c)
    qi = 0
    while qi < len(queue):
        cur = queue[qi]
        qi += 1
        for p in commit_parents(repo, cur):
            if p not in dist:
                dist[p] = dist[cur] + 1
                queue.append(p)
    shallow_set = set()
    for s in shallow:
        sc = repo.commit_of(s)
        if sc is not None:
            shallow_set.add(sc)
    held, held_commits = _held_set(repo, haves, shallow_set)
    limit = None
    if depth is not None:
        if shallow:
            best = None
            for sc in shallow_set:
                if sc in dist:
                    cand = dist[sc] + depth - 1
                    best = cand if best is None else max(best, cand)
            limit = best if best is not None else depth - 1
        else:
            limit = depth - 1
    included = set()
    for c, d in dist.items():
        if c in held_commits:
            continue
        if limit is not None and d > limit:
            continue
        included.add(c)
    boundary = set()
    if limit is not None:
        for c in included:
            if dist[c] == limit:
                boundary.add(c)
    unshallow = []
    if shallow:
        covered = included | held_commits
        for s in shallow:
            sc = repo.commit_of(s)
            if sc is None or sc not in covered:
                continue
            parents = commit_parents(repo, sc)
            if all(p in covered for p in parents):
                unshallow.append(s)
    # Collect the pack objects: the included commits and their trees/blobs,
    # plus any tag object a want named, minus everything the client holds.
    objs = {}
    seen = set()

    def add(oid):
        if oid in seen or oid in held:
            return
        ent = repo.get_obj(oid)
        if ent is None:
            return
        seen.add(oid)
        objs[oid] = ent
        if ent[0] == "commit":
            tree = parse_commit(ent[1])["tree"]
            if tree:
                add(tree)
        elif ent[0] == "tree":
            for _mode, _name, sub in parse_tree(ent[1]):
                add(sub)
        elif ent[0] == "tag":
            add(parse_tag(ent[1])["object"])

    for c in sorted(included):
        add(c)
    for w in wants:
        ent = repo.get_obj(w)
        if ent is not None and ent[0] == "tag":
            add(w)
    pack = write_pack([(objs[o][0], objs[o][1]) for o in sorted(objs)])
    result = (pack, sorted(boundary), sorted(unshallow))
    repo.fetch_cache[cache_key] = result
    return result


def fetch_v2_body(repo, wants, haves, depth, shallow):
    pack, sh, unsh = compute_fetch(repo, wants, haves, depth, shallow)
    out = bytearray()
    # Protocol v2 fetch response: sections are separated by DELIM (0001),
    # not FLUSH; only the final terminator is a FLUSH. The acknowledgments
    # section is sent ONLY when the client sent haves (there is a
    # negotiation to answer). A fresh clone sends no haves, and real git
    # expects the response to start with shallow-info/packfile directly —
    # it dies with "expected 'packfile', received 'acknowledgments'" if an
    # acknowledgments section is present with no haves. The kit's parser
    # accepts a missing acknowledgments section.
    if haves:
        out += pkt("acknowledgments\n") + pkt("NAK\n") + DELIM
    if depth is not None:
        out += pkt("shallow-info\n")
        for s in sh:
            out += pkt("shallow %s\n" % s)
        for u in unsh:
            out += pkt("unshallow %s\n" % u)
        out += DELIM
    out += pkt("packfile\n")
    out += sideband_pack(pack)
    out += FLUSH
    return bytes(out)


def fetch_v0_body(repo, wants, haves, depth, shallow):
    pack, sh, unsh = compute_fetch(repo, wants, haves, depth, shallow)
    out = bytearray()
    out += pkt("NAK\n")
    for s in sh:
        out += pkt("shallow %s\n" % s)
    for u in unsh:
        out += pkt("unshallow %s\n" % u)
    out += sideband_pack(pack)
    out += FLUSH
    return bytes(out)


def _pkt_lines_until_flush(data):
    """Parse pkt-lines until the first flush. Returns (packets, offset)."""
    packets = []
    pos = 0
    while pos < len(data):
        if pos + 4 > len(data):
            raise ValueError("truncated pkt-line header")
        ln = int(data[pos:pos + 4], 16)
        if ln == 0:
            pos += 4
            return packets, pos
        if ln == 1:
            packets.append(("delim", None))
            pos += 4
        elif ln < 4:
            raise ValueError("bad pkt-line length")
        else:
            if pos + ln > len(data):
                raise ValueError("truncated pkt-line")
            packets.append(("data", data[pos + 4:pos + ln]))
            pos += ln
    raise ValueError("no flush in pkt-line stream")


def parse_ls_refs_request(body):
    packets, _ = _pkt_lines_until_flush(body)
    peel = False
    symrefs = False
    unborn = False
    prefixes = []
    for kind, payload in packets:
        if kind != "data":
            continue
        line = payload.decode("utf-8", "replace").strip()
        if line == "peel":
            peel = True
        elif line == "symrefs":
            symrefs = True
        elif line == "unborn":
            unborn = True
        elif line.startswith("ref-prefix "):
            prefixes.append(line[len("ref-prefix "):])
    return prefixes, peel, symrefs, unborn


def parse_fetch_v2_request(body):
    packets, _ = _pkt_lines_until_flush(body)
    wants, haves, shallow = [], [], []
    depth = None
    after_delim = False
    for kind, payload in packets:
        if kind == "delim":
            after_delim = True
            continue
        if kind != "data":
            continue
        line = payload.decode("utf-8", "replace").strip()
        if not after_delim:
            continue
        if line.startswith("want "):
            wants.append(line[5:].split()[0])
        elif line.startswith("have "):
            haves.append(line[5:].split()[0])
        elif line.startswith("shallow "):
            shallow.append(line[8:].split()[0])
        elif line.startswith("deepen "):
            depth = int(line[7:])
    return wants, haves, depth, shallow


def parse_fetch_v0_request(body):
    packets1, off = _pkt_lines_until_flush(body)
    packets2, _ = _pkt_lines_until_flush(body[off:])
    wants, haves, shallow = [], [], []
    depth = None
    for kind, payload in packets1:
        if kind != "data":
            continue
        line = payload.decode("utf-8", "replace").strip()
        if line.startswith("want "):
            wants.append(line[5:].split()[0])
        elif line.startswith("shallow "):
            shallow.append(line[8:].split()[0])
        elif line.startswith("deepen "):
            depth = int(line[7:])
    for kind, payload in packets2:
        if kind != "data":
            continue
        line = payload.decode("utf-8", "replace").strip()
        if line.startswith("have "):
            haves.append(line[5:].split()[0])
    return wants, haves, depth, shallow


def parse_receive_pack_request(body):
    packets, off = _pkt_lines_until_flush(body)
    commands = []
    for kind, payload in packets:
        if kind != "data":
            continue
        line = payload.decode("utf-8", "replace")
        if "\0" in line:
            line = line.split("\0", 1)[0]
        line = line.strip()
        parts = line.split(" ")
        if len(parts) >= 3:
            commands.append((parts[0], parts[1], parts[2]))
    return commands, body[off:]


def receive_pack_body(results, unpack_ok):
    # Report-status inside sideband band 1 is itself pkt-lined ("unpack ok\n",
    # "ok <ref>\n" as pkt-lines) AND terminated by a FLUSH pkt-line inside
    # band 1: real git's report parser reads the band-1 stream as pkt-lines
    # and treats EOF (outer flush only) as "the remote end hung up
    # unexpectedly"; the inner flush is the clean end-of-report. The kit's
    # parser filters to data packets only, so the inner flush is harmless.
    inner = bytearray()
    inner += pkt("unpack %s\n" % ("ok" if unpack_ok else "error"))
    for ref, ok, reason in results:
        if ok:
            inner += pkt("ok %s\n" % ref)
        else:
            inner += pkt("ng %s %s\n" % (ref, reason))
    inner += FLUSH
    out = bytearray()
    out += sideband_pack(bytes(inner), band=1)
    out += FLUSH
    return bytes(out)


def handle_receive_pack(repo, body):
    try:
        commands, pack = parse_receive_pack_request(body)
    except ValueError:
        return receive_pack_body([], False)
    unpack_ok = True
    new_objects = {}
    if pack:
        try:
            new_objects = read_pack(
                pack, resolve_base=lambda oid: repo.get_obj(oid))
        except ValueError:
            unpack_ok = False
    results = []
    if unpack_ok:
        for oid, ent in new_objects.items():
            repo.objects[oid] = ent
        for old, new, ref in commands:
            cur = repo.refs.get(ref)
            if new == ZERO_OID:
                if cur is None:
                    results.append((ref, False, "ref does not exist"))
                elif old != ZERO_OID and old != cur:
                    results.append((ref, False, "old value does not match"))
                else:
                    del repo.refs[ref]
                    results.append((ref, True, ""))
                continue
            if cur is None:
                if old != ZERO_OID:
                    results.append((ref, False, "old value does not match"))
                    continue
            else:
                if old != cur:
                    results.append((ref, False, "old value does not match"))
                    continue
                if old == new:
                    results.append((ref, True, ""))
                    continue
            if old != ZERO_OID and not is_ancestor(repo, old, new):
                results.append((ref, False, "non-fast-forward"))
                continue
            if repo.commit_of(new) is None:
                results.append((ref, False, "object not found"))
                continue
            repo.refs[ref] = new
            results.append((ref, True, ""))
        repo.invalidate_cache()
    else:
        for _old, _new, ref in commands:
            results.append((ref, False, "unpack error"))
    return receive_pack_body(results, unpack_ok)

# ---------------------------------------------------------------- REST v3

def _json_bytes(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode()


def _err(status, message):
    return (status, "application/json", _json_bytes({"message": message}), {})


def _ok(status, obj, extra=None):
    return (status, "application/json", _json_bytes(obj), extra or {})


def _page_links(host, path, query, page, per_page, total):
    """GitHub-style Link header. Returns the header value or None."""
    last_page = max(1, -(-total // per_page))
    if last_page <= 1:
        return None
    def url(p):
        qs = dict(query)
        qs["page"] = [str(p)]
        qs["per_page"] = [str(per_page)]
        flat = "&".join("%s=%s" % (k, v[0]) for k, v in sorted(qs.items()))
        return "http://%s%s?%s" % (host, path, flat)
    parts = []
    if page < last_page:
        parts.append('<%s>; rel="next"' % url(page + 1))
        parts.append('<%s>; rel="last"' % url(last_page))
    if page > 1:
        parts.append('<%s>; rel="first"' % url(1))
        parts.append('<%s>; rel="prev"' % url(page - 1))
    return ", ".join(parts) if parts else None


def _paginate(items, query):
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    try:
        page = int(query.get("page", ["1"])[0])
    except ValueError:
        page = 1
    per_page = max(1, min(per_page, 100))
    page = max(1, page)
    start = (page - 1) * per_page
    return items[start:start + per_page], page, per_page


def _parse_body(raw):
    if not raw:
        return {}
    try:
        val = json.loads(raw.decode("utf-8"))
    except (ValueError, UnicodeDecodeError):
        return None
    if not isinstance(val, dict):
        return None
    return val


def _resolve_ref(repo, ref):
    """A branch name, a full ref, or a commit oid -> commit oid or None."""
    if ref is None:
        return repo.default_tip()
    if ref in repo.refs:
        return repo.refs[ref]
    full = "refs/heads/" + ref
    if full in repo.refs:
        return repo.refs[full]
    if re.fullmatch(r"[0-9a-f]{40}", ref or ""):
        return repo.commit_of(ref)
    return None


def _contents_put(repo, path, body, method):
    message = body.get("message", "")
    content_b64 = body.get("content")
    branch = body.get("branch") or repo.default_branch
    sha = body.get("sha")
    if content_b64 is None:
        return _err(422, "content is required")
    try:
        raw = base64.b64decode(content_b64)
    except Exception:
        return _err(400, "content is not valid base64")
    branch_ref = "refs/heads/" + branch
    base_tip = repo.refs.get(branch_ref)
    if base_tip is None and branch != repo.default_branch:
        # A new branch starts from the default branch tip.
        base_tip = repo.default_tip()
    base_tree = commit_tree(repo, base_tip) if base_tip else None
    cur = tree_get(repo, base_tree, path) if base_tree is not None else None
    if cur is not None and cur[0] != "blob":
        return _err(422, "path is a directory")
    if sha is not None:
        if cur is None or cur[1] != sha:
            return _err(409, "sha does not match the current blob")
    else:
        if cur is not None:
            return _err(422, "sha is required to update a file")
    blob_oid = repo.put_obj("blob", raw)
    new_tree = tree_set(repo, base_tree, path, blob_oid)
    if new_tree is None:
        new_tree = repo.put_obj("tree", encode_tree([]))
    parents = [base_tip] if base_tip else []
    commit_oid = make_commit(repo, new_tree, parents, message or "Update %s" % path)
    repo.refs[branch_ref] = commit_oid
    repo.invalidate_cache()
    created = cur is None
    content = {
        "name": path.rsplit("/", 1)[-1],
        "path": path,
        "sha": blob_oid,
        "size": len(raw),
        "url": "",
        "html_url": "",
        "git_url": "",
        "download_url": "",
        "type": "file",
        "encoding": "base64",
        "content": base64.b64encode(raw).decode(),
        "_links": {"self": "", "git": "", "html": ""},
    }
    commit = {"sha": commit_oid, "message": message or "",
              "author": {"name": VIEWER_NAME, "email": VIEWER_EMAIL,
                         "date": FIXED_ISO},
              "committer": {"name": VIEWER_NAME, "email": VIEWER_EMAIL,
                            "date": FIXED_ISO},
              "tree": {"sha": new_tree}, "parents": [{"sha": p} for p in parents]}
    return _ok(201 if created else 200, {"content": content, "commit": commit})


def handle_rest(method, path, query, raw_body, host):
    """REST v3. Returns (status, content_type, body_bytes, extra_headers)."""
    segs = [unquote(s) for s in path.split("/") if s != ""]
    # /api/v3/...
    if not segs or segs[0] != "api" or len(segs) < 2 or segs[1] != "v3":
        return _err(404, "Not Found")
    rest = segs[2:]

    # -- root and meta -------------------------------------------------
    if method == "GET" and rest == []:
        return _ok(200, {
            "current_user_url": "https://example.invalid/api/v3/user",
            "repository_url": "https://example.invalid/api/v3/repos/{owner}/{repo}",
            "user_url": "https://example.invalid/api/v3/users/{user}",
        }, {"X-OAuth-Scopes": "repo, user"})
    if method == "GET" and rest == ["meta"]:
        return _ok(200, {"installed_version": "1.0.0",
                         "verifiable_password_authentication": True})
    if method == "GET" and rest == ["user"]:
        return _ok(200, {"login": VIEWER, "id": VIEWER_ID, "node_id": gid("User", VIEWER_ID),
                         "name": VIEWER_NAME, "email": VIEWER_EMAIL,
                         "type": "User", "site_admin": False})

    # -- /user/repos ----------------------------------------------------
    if rest[:2] == ["user", "repos"]:
        if method == "GET" and len(rest) == 2:
            repos = [REPOS[k] for k in sorted(REPOS, key=lambda k: REPOS[k].id)
                     if k[0] == VIEWER]
            page_items, page, per_page = _paginate([repo_json(r) for r in repos], query)
            link = _page_links(host, path, query, page, per_page, len(repos))
            return _ok(200, page_items, {"Link": link} if link else {})
        if method == "POST" and len(rest) == 2:
            body = _parse_body(raw_body)
            if body is None:
                return _err(400, "Invalid JSON body")
            name = body.get("name")
            if not name or not isinstance(name, str):
                return _err(422, "name is required")
            if get_repo(VIEWER, name) is not None:
                return _err(422, "Repository already exists")
            repo = create_repo_obj(name, owner=VIEWER,
                                   description=body.get("description") or "",
                                   private=bool(body.get("private", False)))
            return _ok(201, repo_json(repo))
        return _err(404, "Not Found")

    # -- /repos/{owner}/{repo}/... --------------------------------------
    if len(rest) >= 3 and rest[0] == "repos":
        owner, name = rest[1], rest[2]
        repo = get_repo(owner, name)
        if repo is None or owner != VIEWER:
            return _err(404, "Not Found")
        tail = rest[3:]

        if tail == []:
            if method == "GET":
                return _ok(200, repo_json(repo))
            if method == "PATCH":
                body = _parse_body(raw_body)
                if body is None:
                    return _err(400, "Invalid JSON body")
                if "description" in body:
                    repo.description = body.get("description") or ""
                if isinstance(body.get("default_branch"), str) \
                        and body["default_branch"] in [r[len("refs/heads/"):]
                        for r in repo.refs if r.startswith("refs/heads/")]:
                    repo.default_branch = body["default_branch"]
                return _ok(200, repo_json(repo))
            if method == "DELETE":
                del REPOS[(owner, name)]
                return (204, "application/json", b"", {})
            return _err(404, "Not Found")

        if tail == ["branches"] and method == "GET":
            out = [branch_json(repo, r) for r in sorted(repo.refs)
                   if r.startswith("refs/heads/")]
            return _ok(200, out)

        if len(tail) == 2 and tail[0] == "branches" and method == "GET":
            refname = "refs/heads/" + tail[1]
            if refname not in repo.refs:
                return _err(404, "Not Found")
            return _ok(200, branch_json(repo, refname))

        if tail == ["commits"] and method == "GET":
            ref = query.get("sha", [None])[0]
            tip = _resolve_ref(repo, ref)
            out = []
            if tip is not None:
                seen = set()
                stack = [tip]
                order = []
                while stack:
                    cur = stack.pop(0)
                    if cur in seen:
                        continue
                    seen.add(cur)
                    order.append(cur)
                    stack.extend(commit_parents(repo, cur))
                for c in order:
                    r = repo.resolve(c)
                    if r is None:
                        continue
                    msg = parse_commit(r[2])["message"]
                    out.append({
                        "sha": c,
                        "commit": {"message": msg,
                                   "author": {"name": VIEWER_NAME,
                                              "email": VIEWER_EMAIL,
                                              "date": FIXED_ISO},
                                   "committer": {"name": VIEWER_NAME,
                                                 "email": VIEWER_EMAIL,
                                                 "date": FIXED_ISO}},
                        "author": {"login": VIEWER, "id": VIEWER_ID},
                        "committer": {"login": VIEWER, "id": VIEWER_ID},
                        "parents": [{"sha": p} for p in commit_parents(repo, c)],
                        "url": "", "html_url": "",
                    })
            page_items, page, per_page = _paginate(out, query)
            link = _page_links(host, path, query, page, per_page, len(out))
            return _ok(200, page_items, {"Link": link} if link else {})

        if tail[:2] == ["git", "refs"] and method == "GET" and len(tail) >= 4 \
                and tail[2] == "heads":
            branch = "/".join(tail[3:])
            refname = "refs/heads/" + branch
            if refname not in repo.refs:
                return _err(404, "Not Found")
            return _ok(200, {"ref": refname,
                             "node_id": gid("Ref", repo.id, refname),
                             "url": "",
                             "object": {"sha": repo.refs[refname],
                                        "type": "commit", "url": ""}})

        if tail == ["git", "refs"] and method == "POST":
            body = _parse_body(raw_body)
            if body is None:
                return _err(400, "Invalid JSON body")
            ref = body.get("ref")
            sha = body.get("sha")
            if not ref or not sha:
                return _err(422, "ref and sha are required")
            if ref in repo.refs:
                return _err(422, "Reference already exists")
            if repo.commit_of(sha) is None:
                return _err(422, "Object does not exist")
            repo.refs[ref] = repo.commit_of(sha)
            repo.invalidate_cache()
            return _ok(201, {"ref": ref,
                             "node_id": gid("Ref", repo.id, ref),
                             "url": "",
                             "object": {"sha": repo.refs[ref],
                                        "type": "commit", "url": ""}})

        if tail and tail[0] == "contents":
            cpath = "/".join(tail[1:])
            if method in ("PUT", "DELETE"):
                body = _parse_body(raw_body)
                if body is None:
                    return _err(400, "Invalid JSON body")
                if method == "PUT":
                    return _contents_put(repo, cpath, body, method)
                # DELETE contents
                branch = body.get("branch") or repo.default_branch
                sha = body.get("sha")
                branch_ref = "refs/heads/" + branch
                base_tip = repo.refs.get(branch_ref)
                if base_tip is None:
                    return _err(404, "Not Found")
                base_tree = commit_tree(repo, base_tip)
                cur = tree_get(repo, base_tree, cpath) if base_tree else None
                if cur is None or cur[0] != "blob":
                    return _err(404, "Not Found")
                if sha is not None and cur[1] != sha:
                    return _err(409, "sha does not match the current blob")
                new_tree = tree_set(repo, base_tree, cpath, None)
                if new_tree is None:
                    new_tree = repo.put_obj("tree", encode_tree([]))
                commit_oid = make_commit(repo, new_tree, [base_tip],
                                         body.get("message") or "Delete %s" % cpath)
                repo.refs[branch_ref] = commit_oid
                repo.invalidate_cache()
                return _ok(200, {"commit": {"sha": commit_oid,
                                            "message": body.get("message") or ""}})
            if method == "GET":
                ref = query.get("ref", [None])[0]
                tip = _resolve_ref(repo, ref)
                if tip is None:
                    return _err(404, "Not Found")
                tree = commit_tree(repo, tip)
                got = tree_get(repo, tree, cpath) if tree else None
                if got is None:
                    return _err(404, "Not Found")
                if got[0] == "tree":
                    children = tree_list(repo, tree, cpath) or []
                    out = []
                    for mode, nm, oid, typ in children:
                        ent = repo.get_obj(oid)
                        out.append({"type": "dir" if typ == "tree" else "file",
                                    "name": nm,
                                    "path": (cpath + "/" + nm) if cpath else nm,
                                    "sha": oid,
                                    "size": len(ent[1]) if ent and typ == "file" else 0,
                                    "url": "", "html_url": "", "git_url": "",
                                    "download_url": ""})
                    return _ok(200, out)
                ent = repo.get_obj(got[1])
                raw = ent[1] if ent else b""
                return _ok(200, {"type": "file",
                                 "name": cpath.rsplit("/", 1)[-1],
                                 "path": cpath,
                                 "sha": got[1],
                                 "size": len(raw),
                                 "url": "", "html_url": "", "git_url": "",
                                 "download_url": "",
                                 "encoding": "base64",
                                 "content": base64.b64encode(raw).decode(),
                                 "_links": {"self": "", "git": "", "html": ""}})
            return _err(404, "Not Found")

        if tail == ["labels"] and method == "POST":
            body = _parse_body(raw_body)
            if body is None:
                return _err(400, "Invalid JSON body")
            name = body.get("name")
            if not name:
                return _err(422, "name is required")
            if name in repo.labels:
                return _err(422, "Label already exists")
            label = {"id": _next(NEXT_LABEL_ID), "name": name,
                     "color": body.get("color") or "ededed",
                     "description": body.get("description") or "",
                     "default": False, "url": ""}
            repo.labels[name] = label
            return _ok(201, label)
        if tail == ["labels"] and method == "GET":
            return _ok(200, list(repo.labels.values()))

        if tail == ["issues"] and method == "POST":
            body = _parse_body(raw_body)
            if body is None:
                return _err(400, "Invalid JSON body")
            for lab in body.get("labels") or []:
                if lab not in repo.labels:
                    return _err(422, "Label does not exist: %s" % lab)
            issue = create_issue_obj(repo, body.get("title") or "",
                                     body.get("body") or "",
                                     body.get("labels") or [])
            return _ok(201, issue_json(repo, issue))
        if tail == ["issues"] and method == "GET":
            state = query.get("state", ["open"])[0]
            sort = query.get("sort", ["created"])[0]
            direction = query.get("direction", ["desc"])[0]
            items = list(repo.issues.values())
            if state in ("open", "closed"):
                items = [i for i in items if i["state"] == state]
            reverse = direction != "asc"
            items.sort(key=lambda i: i["seq"], reverse=reverse)
            out = [issue_json(repo, i) for i in items]
            page_items, page, per_page = _paginate(out, query)
            link = _page_links(host, path, query, page, per_page, len(out))
            return _ok(200, page_items, {"Link": link} if link else {})

        if len(tail) == 2 and tail[0] == "issues" and tail[1].isdigit():
            num = int(tail[1])
            issue = repo.issues.get(num)
            if issue is None:
                return _err(404, "Not Found")
            if method == "GET":
                return _ok(200, issue_json(repo, issue))
            if method == "PATCH":
                body = _parse_body(raw_body)
                if body is None:
                    return _err(400, "Invalid JSON body")
                if "state" in body and body["state"] in ("open", "closed"):
                    issue["state"] = body["state"]
                    issue["closed_at"] = FIXED_ISO if body["state"] == "closed" else None
                if "title" in body:
                    issue["title"] = body["title"]
                if "body" in body:
                    issue["body"] = body["body"]
                if "labels" in body:
                    for lab in body["labels"] or []:
                        if lab not in repo.labels:
                            return _err(422, "Label does not exist: %s" % lab)
                    issue["labels"] = list(body["labels"] or [])
                return _ok(200, issue_json(repo, issue))
            return _err(404, "Not Found")

        if len(tail) == 3 and tail[0] == "issues" and tail[1].isdigit() \
                and tail[2] == "comments":
            num = int(tail[1])
            if num not in repo.issues:
                return _err(404, "Not Found")
            if method == "POST":
                body = _parse_body(raw_body)
                if body is None:
                    return _err(400, "Invalid JSON body")
                comment = create_comment_obj(repo, num, body.get("body") or "")
                return _ok(201, comment_json(repo, comment))
            if method == "GET":
                out = [comment_json(repo, c) for c in repo.comments.get(num, [])]
                return _ok(200, out)
            return _err(404, "Not Found")

        if tail == ["pulls"] and method == "POST":
            body = _parse_body(raw_body)
            if body is None:
                return _err(400, "Invalid JSON body")
            head = body.get("head")
            base = body.get("base")
            if not head or not base:
                return _err(422, "head and base are required")
            if ("refs/heads/" + head) not in repo.refs \
                    or ("refs/heads/" + base) not in repo.refs:
                return _err(422, "head or base branch does not exist")
            pr = create_pr_obj(repo, body.get("title") or "",
                               body.get("body") or "", head, base)
            if pr is None:
                return _err(422, "head or base branch does not exist")
            return _ok(201, pr_json(repo, pr))
        if tail == ["pulls"] and method == "GET":
            state = query.get("state", ["open"])[0]
            items = list(repo.pulls.values())
            if state == "open":
                items = [p for p in items if p["state"] == "open"]
            elif state == "closed":
                items = [p for p in items if p["state"] == "closed"]
            items.sort(key=lambda p: p["seq"])
            out = [pr_json(repo, p) for p in items]
            page_items, page, per_page = _paginate(out, query)
            link = _page_links(host, path, query, page, per_page, len(out))
            return _ok(200, page_items, {"Link": link} if link else {})

        if len(tail) == 2 and tail[0] == "pulls" and tail[1].isdigit():
            num = int(tail[1])
            pr = repo.pulls.get(num)
            if pr is None:
                return _err(404, "Not Found")
            if method == "GET":
                return _ok(200, pr_json(repo, pr))
            return _err(404, "Not Found")

        if len(tail) == 3 and tail[0] == "pulls" and tail[1].isdigit() \
                and tail[2] == "files" and method == "GET":
            num = int(tail[1])
            pr = repo.pulls.get(num)
            if pr is None:
                return _err(404, "Not Found")
            out = []
            for fpath, status, old_oid, new_oid in pr_diff(repo, pr):
                add, dele = line_counts(repo, old_oid, new_oid)
                entry = {"filename": fpath, "status": status,
                         "additions": add, "deletions": dele,
                         "changes": add + dele,
                         "sha": new_oid or old_oid or "",
                         "blob_url": "", "raw_url": "", "contents_url": ""}
                out.append(entry)
            return _ok(200, out)

        if len(tail) == 3 and tail[0] == "pulls" and tail[1].isdigit() \
                and tail[2] == "merge" and method == "PUT":
            num = int(tail[1])
            pr = repo.pulls.get(num)
            if pr is None:
                return _err(404, "Not Found")
            body = _parse_body(raw_body)
            if body is None:
                return _err(400, "Invalid JSON body")
            status, payload = merge_pr_obj(repo, pr)
            return _ok(status, payload) if status == 200 else _err(status, payload["message"])

        return _err(404, "Not Found")

    return _err(404, "Not Found")

# ---------------------------------------------------------------- GraphQL v4

class GqlFieldError(Exception):
    pass


def gql_tokenize(src):
    tokens = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c in " \t\r\n,":
            i += 1
            continue
        if c == "#":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if src[i:i + 3] == "...":
            tokens.append(("...", "..."))
            i += 3
            continue
        if c in "{}():!$[]=":
            tokens.append((c, c))
            i += 1
            continue
        if c == '"':
            if src[i:i + 3] == '"""':
                j = src.find('"""', i + 3)
                if j < 0:
                    raise ValueError("unterminated block string")
                tokens.append(("STRING", src[i + 3:j]))
                i = j + 3
                continue
            j = i + 1
            out = []
            while j < n and src[j] != '"':
                if src[j] == "\\":
                    j += 1
                    if j >= n:
                        break
                    esc = src[j]
                    out.append({"n": "\n", "t": "\t", "r": "\r", '"': '"',
                                "\\": "\\", "/": "/"}.get(esc, esc))
                else:
                    out.append(src[j])
                j += 1
            tokens.append(("STRING", "".join(out)))
            i = j + 1
            continue
        if c.isdigit() or (c == "-" and i + 1 < n and src[i + 1].isdigit()):
            j = i
            while j < n and (src[j].isdigit() or src[j] in ".eE+-"):
                j += 1
            txt = src[i:j]
            try:
                val = float(txt) if ("." in txt or "e" in txt or "E" in txt) else int(txt)
            except ValueError:
                raise ValueError("bad number %r" % txt)
            tokens.append(("NUMBER", val))
            i = j
            continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (src[j].isalnum() or src[j] == "_"):
                j += 1
            tokens.append(("NAME", src[i:j]))
            i = j
            continue
        raise ValueError("unexpected character %r" % c)
    tokens.append(("EOF", None))
    return tokens


class GqlParser:
    def __init__(self, tokens):
        self.toks = tokens
        self.i = 0

    def peek(self):
        return self.toks[self.i]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def expect(self, kind, val=None):
        t = self.next()
        if t[0] != kind or (val is not None and t[1] != val):
            raise ValueError("expected %s %s, got %r" % (kind, val, t))
        return t

    def parse_document(self):
        ops = []
        while self.peek()[0] != "EOF":
            ops.append(self.parse_operation())
        return ops

    def parse_operation(self):
        if self.peek()[0] == "{":
            return {"kind": "query", "name": None,
                    "selections": self.parse_selection_set()}
        kind = self.expect("NAME")[1]
        name = None
        if self.peek()[0] == "NAME":
            name = self.next()[1]
        if self.peek()[0] == "(":
            self._skip_parens()
        return {"kind": kind, "name": name,
                "selections": self.parse_selection_set()}

    def _skip_parens(self):
        self.expect("(")
        depth = 1
        while depth:
            t = self.next()
            if t[0] == "(":
                depth += 1
            elif t[0] == ")":
                depth -= 1

    def parse_selection_set(self):
        self.expect("{")
        sels = []
        while self.peek()[0] != "}":
            sels.append(self.parse_selection())
        self.expect("}")
        return sels

    def parse_selection(self):
        if self.peek()[0] == "...":
            self.next()
            t = self.peek()
            if t[0] == "NAME" and t[1] == "on":
                self.next()
                tname = self.expect("NAME")[1]
                return {"fragment": "on", "type": tname,
                        "selections": self.parse_selection_set()}
            fname = self.expect("NAME")[1]
            return {"fragment": fname, "selections": []}
        name = self.expect("NAME")[1]
        alias = None
        if self.peek()[0] == ":":
            self.next()
            alias = name
            name = self.expect("NAME")[1]
        args = {}
        if self.peek()[0] == "(":
            args = self.parse_args()
        sels = []
        if self.peek()[0] == "{":
            sels = self.parse_selection_set()
        return {"field": name, "alias": alias, "args": args, "selections": sels}

    def parse_args(self):
        self.expect("(")
        args = {}
        while self.peek()[0] != ")":
            name = self.expect("NAME")[1]
            self.expect(":")
            args[name] = self.parse_value()
        self.expect(")")
        return args

    def parse_value(self):
        t = self.peek()
        if t[0] == "$":
            self.next()
            return ("var", self.expect("NAME")[1])
        if t[0] == "STRING":
            self.next()
            return t[1]
        if t[0] == "NUMBER":
            self.next()
            return t[1]
        if t[0] == "[":
            self.next()
            vals = []
            while self.peek()[0] != "]":
                vals.append(self.parse_value())
            self.expect("]")
            return vals
        if t[0] == "{":
            self.next()
            obj = {}
            while self.peek()[0] != "}":
                k = self.expect("NAME")[1]
                self.expect(":")
                obj[k] = self.parse_value()
            self.expect("}")
            return obj
        if t[0] == "NAME":
            self.next()
            if t[1] == "true":
                return True
            if t[1] == "false":
                return False
            if t[1] == "null":
                return None
            return ("enum", t[1])
        raise ValueError("unexpected value token %r" % (t,))


def _resolve_value(v, variables):
    if isinstance(v, tuple):
        if v[0] == "var":
            return variables.get(v[1])
        if v[0] == "enum":
            return v[1]
    if isinstance(v, list):
        return [_resolve_value(x, variables) for x in v]
    if isinstance(v, dict):
        return {k: _resolve_value(x, variables) for k, x in v.items()}
    return v


def _repo_by_id(rid):
    for repo in REPOS.values():
        if repo.id == rid:
            return repo
    return None


def _decode_global_id(value):
    """Returns (kind, repo_id, number_or_id) or None."""
    if not isinstance(value, str):
        return None
    raw = ungid(value)
    if raw is None:
        return None
    parts = raw.split(":")
    if len(parts) < 2:
        return None
    return parts


def _user_tag():
    return {"_gtype": "User", "login": VIEWER, "id": VIEWER_ID}


def _repo_tag(repo):
    return {"_gtype": "Repository", "_repo": repo}


def _issue_tag(repo, issue):
    return {"_gtype": "Issue", "_repo": repo, "_issue": issue}


def _pr_tag(repo, pr):
    return {"_gtype": "PullRequest", "_repo": repo, "_pr": pr}


def _comment_tag(repo, comment):
    return {"_gtype": "IssueComment", "_repo": repo, "_comment": comment}


def _cursor(num):
    return base64.urlsafe_b64encode(str(num).encode()).decode().rstrip("=")


def _uncursor(cur):
    try:
        padded = cur + "=" * (-len(cur) % 4)
        return int(base64.urlsafe_b64decode(padded).decode())
    except Exception:
        return None


def _issues_connection(repo, args):
    states = args.get("states")
    order_by = args.get("orderBy") or {}
    direction = order_by.get("direction") or "DESC"
    first = args.get("first")
    after = args.get("after")
    items = list(repo.issues.values())
    if states:
        wanted = set(str(s).lower() for s in states)
        items = [i for i in items if i["state"].lower() in wanted]
    items.sort(key=lambda i: i["seq"], reverse=(str(direction).upper() == "DESC"))
    if after is not None:
        after_num = _uncursor(after)
        if after_num is not None:
            idx = next((k for k, it in enumerate(items)
                        if it["number"] == after_num), None)
            if idx is not None:
                items = items[idx + 1:]
    if first is not None:
        page = items[:first]
        has_next = len(items) > first
    else:
        page = items
        has_next = False
    end_cursor = _cursor(page[-1]["number"]) if page else None
    return {"_gtype": "IssueConnection",
            "nodes": [_issue_tag(repo, i) for i in page],
            "pageInfo": {"_gtype": "PageInfo", "hasNextPage": has_next,
                         "endCursor": end_cursor}}


def _prs_connection(repo, args):
    first = args.get("first")
    items = sorted(repo.pulls.values(), key=lambda p: p["seq"])
    if first is not None:
        page = items[:first]
        has_next = len(items) > first
    else:
        page = items
        has_next = False
    end_cursor = _cursor(page[-1]["number"]) if page else None
    return {"_gtype": "PullRequestConnection",
            "nodes": [_pr_tag(repo, p) for p in page],
            "pageInfo": {"_gtype": "PageInfo", "hasNextPage": has_next,
                         "endCursor": end_cursor}}


def _files_connection(repo, pr, args):
    first = args.get("first")
    items = [{"path": p} for (p, _s, _o, _n) in pr_diff(repo, pr)]
    if first is not None:
        page = items[:first]
        has_next = len(items) > first
    else:
        page = items
        has_next = False
    end_cursor = _cursor(len(page)) if page else None
    nodes = [{"_gtype": "ChangedFile", "path": it["path"]} for it in page]
    return {"_gtype": "ChangedFileConnection", "nodes": nodes,
            "pageInfo": {"_gtype": "PageInfo", "hasNextPage": has_next,
                         "endCursor": end_cursor}}


_TYPE_FIELDS = {
    "Issue": ["id", "number", "title", "state", "body", "author", "createdAt",
              "updatedAt", "closedAt", "labels", "comments", "url", "repository"],
    "PullRequest": ["id", "number", "title", "state", "body", "headRefName",
                    "baseRefName", "mergeable", "merged", "files", "author",
                    "createdAt", "updatedAt", "closedAt", "url"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "issue", "issues", "pullRequests", "pullRequest",
                   "description", "createdAt", "updatedAt", "url"],
    "SearchType": None,
}
_TYPE_ENUMS = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "PULLREQUEST", "COMMIT",
                   "DISCUSSION", "CODE", "WIKI", "MARKETPLACE"],
}


def _type_tag(name):
    return {"_gtype": "__Type", "name": name}


def gql_resolve(obj, field, args):
    t = obj.get("_gtype") if isinstance(obj, dict) else None
    if field == "__typename":
        return t if t not in ("User",) else "User"
    if t == "Query":
        if field == "viewer":
            return _user_tag()
        if field == "repository":
            repo = get_repo(args.get("owner"), args.get("name"))
            return _repo_tag(repo) if repo is not None else None
        if field == "node":
            parts = _decode_global_id(args.get("id"))
            if parts is None:
                return None
            kind = parts[0]
            if kind == "Repository" and len(parts) >= 2:
                repo = _repo_by_id(int(parts[1]))
                return _repo_tag(repo) if repo is not None else None
            if kind == "Issue" and len(parts) >= 3:
                repo = _repo_by_id(int(parts[1]))
                if repo is None:
                    return None
                issue = repo.issues.get(int(parts[2]))
                return _issue_tag(repo, issue) if issue is not None else None
            if kind == "PullRequest" and len(parts) >= 3:
                repo = _repo_by_id(int(parts[1]))
                if repo is None:
                    return None
                pr = repo.pulls.get(int(parts[2]))
                return _pr_tag(repo, pr) if pr is not None else None
            return None
        if field == "__type":
            name = args.get("name")
            if name in _TYPE_FIELDS or name in _TYPE_ENUMS:
                return _type_tag(name)
            return None
        raise GqlFieldError('Cannot query field "%s" on type "Query"' % field)
    if t == "Mutation":
        if field == "createIssue":
            inp = args.get("input") or {}
            parts = _decode_global_id(inp.get("repositoryId"))
            if parts is None or parts[0] != "Repository":
                raise GqlFieldError("Repository not found")
            repo = _repo_by_id(int(parts[1]))
            if repo is None:
                raise GqlFieldError("Repository not found")
            issue = create_issue_obj(repo, inp.get("title") or "",
                                     inp.get("body") or "")
            return {"_gtype": "CreateIssuePayload",
                    "issue": _issue_tag(repo, issue)}
        if field == "closeIssue":
            inp = args.get("input") or {}
            parts = _decode_global_id(inp.get("issueId"))
            if parts is None or parts[0] != "Issue":
                raise GqlFieldError("Issue not found")
            repo = _repo_by_id(int(parts[1]))
            if repo is None:
                raise GqlFieldError("Issue not found")
            issue = repo.issues.get(int(parts[2]))
            if issue is None:
                raise GqlFieldError("Issue not found")
            issue["state"] = "closed"
            issue["closed_at"] = FIXED_ISO
            return {"_gtype": "CloseIssuePayload",
                    "issue": _issue_tag(repo, issue)}
        if field == "createPullRequest":
            inp = args.get("input") or {}
            parts = _decode_global_id(inp.get("repositoryId"))
            if parts is None or parts[0] != "Repository":
                raise GqlFieldError("Repository not found")
            repo = _repo_by_id(int(parts[1]))
            if repo is None:
                raise GqlFieldError("Repository not found")
            pr = create_pr_obj(repo, inp.get("title") or "",
                               inp.get("body") or "",
                               inp.get("headRefName") or "",
                               inp.get("baseRefName") or "")
            if pr is None:
                raise GqlFieldError("head or base branch does not exist")
            return {"_gtype": "CreatePullRequestPayload",
                    "pullRequest": _pr_tag(repo, pr)}
        if field == "mergePullRequest":
            inp = args.get("input") or {}
            parts = _decode_global_id(inp.get("pullRequestId"))
            if parts is None or parts[0] != "PullRequest":
                raise GqlFieldError("Pull request not found")
            repo = _repo_by_id(int(parts[1]))
            if repo is None:
                raise GqlFieldError("Pull request not found")
            pr = repo.pulls.get(int(parts[2]))
            if pr is None:
                raise GqlFieldError("Pull request not found")
            status, _payload = merge_pr_obj(repo, pr)
            if status != 200:
                raise GqlFieldError("Pull request cannot be merged")
            return {"_gtype": "MergePullRequestPayload",
                    "pullRequest": _pr_tag(repo, pr)}
        if field == "addComment":
            inp = args.get("input") or {}
            parts = _decode_global_id(inp.get("subjectId"))
            if parts is None or parts[0] != "Issue":
                raise GqlFieldError("Subject not found")
            repo = _repo_by_id(int(parts[1]))
            if repo is None:
                raise GqlFieldError("Subject not found")
            number = int(parts[2])
            if number not in repo.issues:
                raise GqlFieldError("Subject not found")
            comment = create_comment_obj(repo, number, inp.get("body") or "")
            return {"_gtype": "AddCommentPayload",
                    "commentEdge": {"_gtype": "IssueCommentEdge",
                                    "node": _comment_tag(repo, comment)}}
        raise GqlFieldError('Cannot query field "%s" on type "Mutation"' % field)
    if t == "User":
        if field == "login":
            return obj["login"]
        raise GqlFieldError('Cannot query field "%s" on type "User"' % field)
    if t == "Repository":
        repo = obj["_repo"]
        if field == "id":
            return gid("Repository", repo.id)
        if field == "databaseId":
            return repo.id
        if field == "name":
            return repo.name
        if field == "nameWithOwner":
            return "%s/%s" % (repo.owner, repo.name)
        if field == "owner":
            return _user_tag()
        if field == "defaultBranchRef":
            if ("refs/heads/" + repo.default_branch) not in repo.refs:
                return None
            return {"_gtype": "Ref", "name": repo.default_branch}
        if field == "viewerPermission":
            return "ADMIN"
        if field == "hasIssuesEnabled":
            return True
        if field == "issue":
            issue = repo.issues.get(args.get("number"))
            return _issue_tag(repo, issue) if issue is not None else None
        if field == "issues":
            return _issues_connection(repo, args)
        if field == "pullRequests":
            return _prs_connection(repo, args)
        if field == "pullRequest":
            pr = repo.pulls.get(args.get("number"))
            return _pr_tag(repo, pr) if pr is not None else None
        if field == "description":
            return repo.description
        if field == "createdAt" or field == "updatedAt":
            return FIXED_ISO
        if field == "url":
            return "https://example.invalid/%s/%s" % (repo.owner, repo.name)
        raise GqlFieldError('Cannot query field "%s" on type "Repository"' % field)
    if t == "Ref":
        if field == "name":
            return obj["name"]
        raise GqlFieldError('Cannot query field "%s" on type "Ref"' % field)
    if t == "Issue":
        issue = obj["_issue"]
        if field == "id":
            return gid("Issue", obj["_repo"].id, issue["number"])
        if field == "number":
            return issue["number"]
        if field == "title":
            return issue["title"]
        if field == "state":
            return issue["state"].upper()
        if field == "body":
            return issue["body"]
        if field == "author":
            return _user_tag()
        if field == "createdAt" or field == "updatedAt":
            return FIXED_ISO
        if field == "closedAt":
            return issue["closed_at"]
        if field == "url":
            return "https://example.invalid/%s/%s/issues/%d" % (
                obj["_repo"].owner, obj["_repo"].name, issue["number"])
        raise GqlFieldError('Cannot query field "%s" on type "Issue"' % field)
    if t == "PullRequest":
        pr = obj["_pr"]
        if field == "id":
            return gid("PullRequest", obj["_repo"].id, pr["number"])
        if field == "number":
            return pr["number"]
        if field == "title":
            return pr["title"]
        if field == "state":
            return "MERGED" if pr["merged"] else pr["state"].upper()
        if field == "merged":
            return pr["merged"]
        if field == "headRefName":
            return pr["head"]["ref"]
        if field == "baseRefName":
            return pr["base"]["ref"]
        if field == "mergeable":
            if pr["state"] != "open":
                return "UNKNOWN"
            return "MERGEABLE" if not pr_conflicts(obj["_repo"], pr) else "CONFLICTING"
        if field == "files":
            return _files_connection(obj["_repo"], pr, args)
        if field == "body":
            return pr["body"]
        if field == "author":
            return _user_tag()
        if field == "createdAt" or field == "updatedAt":
            return FIXED_ISO
        if field == "closedAt":
            return pr["closed_at"]
        if field == "url":
            return "https://example.invalid/%s/%s/pull/%d" % (
                obj["_repo"].owner, obj["_repo"].name, pr["number"])
        raise GqlFieldError('Cannot query field "%s" on type "PullRequest"' % field)
    if t in ("IssueConnection", "PullRequestConnection", "ChangedFileConnection"):
        if field == "nodes":
            return obj["nodes"]
        if field == "pageInfo":
            return obj["pageInfo"]
        if field == "totalCount":
            return len(obj["nodes"])
        raise GqlFieldError('Cannot query field "%s" on type "%s"' % (field, t))
    if t == "PageInfo":
        if field == "hasNextPage":
            return obj["hasNextPage"]
        if field == "endCursor":
            return obj["endCursor"]
        if field == "hasPreviousPage":
            return False
        if field == "startCursor":
            return None
        raise GqlFieldError('Cannot query field "%s" on type "PageInfo"' % field)
    if t == "ChangedFile":
        if field == "path":
            return obj["path"]
        raise GqlFieldError('Cannot query field "%s" on type "ChangedFile"' % field)
    if t == "__Type":
        name = obj["name"]
        if field == "name":
            return name
        if field == "kind":
            return "ENUM" if name in _TYPE_ENUMS else "OBJECT"
        if field == "fields":
            if name not in _TYPE_FIELDS or _TYPE_FIELDS[name] is None:
                return None
            return [{"_gtype": "__Field", "name": f} for f in _TYPE_FIELDS[name]]
        if field == "enumValues":
            if name not in _TYPE_ENUMS:
                return None
            return [{"_gtype": "__EnumValue", "name": e} for e in _TYPE_ENUMS[name]]
        raise GqlFieldError('Cannot query field "%s" on type "__Type"' % field)
    if t in ("__Field", "__EnumValue"):
        if field == "name":
            return obj["name"]
        raise GqlFieldError('Cannot query field "%s" on type "%s"' % (field, t))
    if t in ("CreateIssuePayload", "CloseIssuePayload"):
        if field == "issue":
            return obj["issue"]
        raise GqlFieldError('Cannot query field "%s" on type "%s"' % (field, t))
    if t in ("CreatePullRequestPayload", "MergePullRequestPayload"):
        if field == "pullRequest":
            return obj["pullRequest"]
        raise GqlFieldError('Cannot query field "%s" on type "%s"' % (field, t))
    if t == "AddCommentPayload":
        if field == "commentEdge":
            return obj["commentEdge"]
        raise GqlFieldError('Cannot query field "%s" on type "AddCommentPayload"' % field)
    if t == "IssueCommentEdge":
        if field == "node":
            return obj["node"]
        raise GqlFieldError('Cannot query field "%s" on type "IssueCommentEdge"' % field)
    if t == "IssueComment":
        comment = obj["_comment"]
        if field == "id":
            return gid("IssueComment", obj["_repo"].id, comment["id"])
        if field == "body":
            return comment["body"]
        if field == "author":
            return _user_tag()
        raise GqlFieldError('Cannot query field "%s" on type "IssueComment"' % field)
    raise GqlFieldError('Cannot query field "%s" on type "%s"' % (field, t))


def _execute_selections(obj, selections, variables, errors):
    out = {}
    if obj is None:
        return None
    for sel in selections:
        if "fragment" in sel:
            if sel["fragment"] == "on":
                if obj.get("_gtype") == sel["type"]:
                    sub = _execute_selections(obj, sel["selections"], variables, errors)
                    if sub:
                        out.update(sub)
            continue
        field = sel["field"]
        alias = sel["alias"] or field
        args = {k: _resolve_value(v, variables) for k, v in sel["args"].items()}
        try:
            val = gql_resolve(obj, field, args)
        except GqlFieldError as e:
            errors.append({"message": str(e), "path": [alias]})
            out[alias] = None
            continue
        if sel["selections"]:
            if val is None:
                out[alias] = None
            elif isinstance(val, list):
                out[alias] = [_execute_selections(item, sel["selections"], variables, errors)
                              if item is not None else None for item in val]
            else:
                out[alias] = _execute_selections(val, sel["selections"], variables, errors)
        else:
            out[alias] = val
    return out


def gql_execute_one(op):
    try:
        query = op.get("query", "")
        variables = op.get("variables") or {}
        if not isinstance(variables, dict):
            variables = {}
        parser = GqlParser(gql_tokenize(query))
        ops = parser.parse_document()
        if not ops:
            return {"data": None, "errors": [{"message": "Empty document"}]}
        operation = ops[0]
        root = {"_gtype": "Mutation" if operation["kind"] == "mutation" else "Query"}
        errors = []
        data = _execute_selections(root, operation["selections"], variables, errors)
        out = {"data": data}
        if errors:
            out["errors"] = errors
        return out
    except Exception as e:
        return {"data": None, "errors": [{"message": "%s: %s" % (type(e).__name__, e)}]}


def handle_graphql(raw_body):
    try:
        doc = json.loads(raw_body.decode("utf-8"))
    except Exception:
        return (400, "application/json",
                _json_bytes({"errors": [{"message": "Invalid JSON body"}]}), {})
    if isinstance(doc, list):
        results = [gql_execute_one(op) if isinstance(op, dict)
                   else {"data": None, "errors": [{"message": "Invalid operation"}]}
                   for op in doc]
        return (200, "application/json", _json_bytes(results), {})
    if isinstance(doc, dict):
        return (200, "application/json", _json_bytes(gql_execute_one(doc)), {})
    return (400, "application/json",
            _json_bytes({"errors": [{"message": "Invalid GraphQL body"}]}), {})

# ---------------------------------------------------------------- MCP

MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a repository for the authenticated user.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Repository name"},
                "description": {"type": "string", "description": "Repository description"},
                "private": {"type": "boolean", "description": "Whether the repository is private"},
                "owner": {"type": "string", "description": "Owner login (defaults to the authenticated user)"},
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
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
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
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
                "title": {"type": "string", "description": "Issue title"},
                "body": {"type": "string", "description": "Issue body"},
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
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
                "state": {"type": "string", "description": "Issue state: open, closed or all"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Create a pull request from a head branch onto a base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
                "title": {"type": "string", "description": "Pull request title"},
                "head": {"type": "string", "description": "Head branch name"},
                "base": {"type": "string", "description": "Base branch name"},
                "body": {"type": "string", "description": "Pull request body"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Merge a pull request with a squash commit onto its base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
                "pull_number": {"type": "integer", "description": "Pull request number"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]


def _mcp_result(obj):
    text = json.dumps(obj, separators=(",", ":"), ensure_ascii=False)
    return {"content": [{"type": "text", "text": text}], "structuredContent": obj}


def _mcp_error_result(message):
    return {"content": [{"type": "text", "text": message}], "isError": True}


def mcp_call_tool(name, arguments):
    """Returns (result, error). Exactly one is not None."""
    tool = None
    for t in MCP_TOOLS:
        if name == t["name"] or name.lower().endswith("__" + t["name"]):
            tool = t
            break
    if tool is None:
        return None, {"code": -32601, "message": "Unknown tool: %s" % name}
    for req in tool["inputSchema"].get("required", []):
        if req not in arguments or arguments[req] is None:
            return _mcp_error_result("Missing required argument: %s" % req), None
    tname = tool["name"]
    if tname == "create_repo":
        rname = arguments.get("name")
        if get_repo(VIEWER, rname) is not None:
            return _mcp_error_result("Repository already exists"), None
        repo = create_repo_obj(rname, owner=VIEWER,
                               description=arguments.get("description") or "",
                               private=bool(arguments.get("private", False)))
        return _mcp_result(repo_json(repo)), None
    if tname == "get_repo":
        repo = get_repo(arguments.get("owner"), arguments.get("repo"))
        if repo is None or arguments.get("owner") != VIEWER:
            return _mcp_error_result("Repository not found"), None
        return _mcp_result(repo_json(repo)), None
    if tname == "create_issue":
        repo = get_repo(arguments.get("owner"), arguments.get("repo"))
        if repo is None or arguments.get("owner") != VIEWER:
            return _mcp_error_result("Repository not found"), None
        labels = arguments.get("labels") or []
        for lab in labels:
            if lab not in repo.labels:
                return _mcp_error_result("Label does not exist: %s" % lab), None
        issue = create_issue_obj(repo, arguments.get("title") or "",
                                 arguments.get("body") or "", labels)
        return _mcp_result(issue_json(repo, issue)), None
    if tname == "list_issues":
        repo = get_repo(arguments.get("owner"), arguments.get("repo"))
        if repo is None or arguments.get("owner") != VIEWER:
            return _mcp_error_result("Repository not found"), None
        state = (arguments.get("state") or "open").lower()
        items = list(repo.issues.values())
        if state in ("open", "closed"):
            items = [i for i in items if i["state"] == state]
        items.sort(key=lambda i: i["seq"])
        out = [issue_json(repo, i) for i in items]
        return _mcp_result(out), None
    if tname == "create_pull_request":
        repo = get_repo(arguments.get("owner"), arguments.get("repo"))
        if repo is None or arguments.get("owner") != VIEWER:
            return _mcp_error_result("Repository not found"), None
        head = arguments.get("head")
        base = arguments.get("base")
        if ("refs/heads/" + head) not in repo.refs \
                or ("refs/heads/" + base) not in repo.refs:
            return _mcp_error_result("head or base branch does not exist"), None
        pr = create_pr_obj(repo, arguments.get("title") or "",
                           arguments.get("body") or "", head, base)
        if pr is None:
            return _mcp_error_result("head or base branch does not exist"), None
        return _mcp_result(pr_json(repo, pr)), None
    if tname == "merge_pull_request":
        repo = get_repo(arguments.get("owner"), arguments.get("repo"))
        if repo is None or arguments.get("owner") != VIEWER:
            return _mcp_error_result("Repository not found"), None
        try:
            num = int(arguments.get("pull_number"))
        except (TypeError, ValueError):
            return _mcp_error_result("pull_number must be an integer"), None
        pr = repo.pulls.get(num)
        if pr is None:
            return _mcp_error_result("Pull request not found"), None
        status, payload = merge_pr_obj(repo, pr)
        if status != 200:
            return _mcp_error_result(payload.get("message", "Merge failed")), None
        return _mcp_result(pr_json(repo, pr)), None
    return None, {"code": -32601, "message": "Unknown tool: %s" % name}


def handle_mcp(raw_body):
    try:
        req = json.loads(raw_body.decode("utf-8"))
    except Exception:
        return (400, "application/json",
                _json_bytes({"jsonrpc": "2.0", "id": None,
                             "error": {"code": -32700, "message": "Parse error"}}), {})
    if not isinstance(req, dict):
        return (400, "application/json",
                _json_bytes({"jsonrpc": "2.0", "id": None,
                             "error": {"code": -32600, "message": "Invalid Request"}}), {})
    method = req.get("method", "")
    req_id = req.get("id")
    params = req.get("params") or {}
    if not isinstance(params, dict):
        params = {}
    if req_id is None:
        # A notification (e.g. notifications/initialized): no response body.
        return (202, "application/json", b"", {})
    if method == "server/discover":
        result = {
            "supportedVersions": ["2026-07-28", "2025-11-25", "2025-06-18",
                                  "2025-03-26", "2024-11-05"],
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "forge-mcp", "version": "1.0.0"},
            "_meta": {"io.modelcontextprotocol/serverInfo":
                      {"name": "forge-mcp", "version": "1.0.0"}},
        }
        return (200, "application/json",
                _json_bytes({"jsonrpc": "2.0", "id": req_id, "result": result}), {})
    if method == "initialize":
        offered = params.get("protocolVersion") or ""
        supported = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26",
                     "2024-11-05"]
        version = offered if offered in supported else "2025-11-25"
        result = {"protocolVersion": version,
                  "capabilities": {"tools": {}},
                  "serverInfo": {"name": "forge-mcp", "version": "1.0.0"}}
        return (200, "application/json",
                _json_bytes({"jsonrpc": "2.0", "id": req_id, "result": result}), {})
    if method == "tools/list":
        return (200, "application/json",
                _json_bytes({"jsonrpc": "2.0", "id": req_id,
                             "result": {"tools": MCP_TOOLS}}), {})
    if method == "tools/call":
        result, error = mcp_call_tool(params.get("name", ""),
                                      params.get("arguments") or {})
        if error is not None:
            return (200, "application/json",
                    _json_bytes({"jsonrpc": "2.0", "id": req_id, "error": error}), {})
        return (200, "application/json",
                _json_bytes({"jsonrpc": "2.0", "id": req_id, "result": result}), {})
    if method == "ping":
        return (200, "application/json",
                _json_bytes({"jsonrpc": "2.0", "id": req_id, "result": {}}), {})
    return (200, "application/json",
            _json_bytes({"jsonrpc": "2.0", "id": req_id,
                         "error": {"code": -32601,
                                   "message": "Method not found: %s" % method}}), {})


# ---------------------------------------------------------------- HTTP server

class ForgeServer(ThreadingHTTPServer):
    # 50 concurrent clones arrive at once; the default listen backlog of 5
    # drops SYNs and stalls the burst for seconds.
    request_queue_size = 128
    daemon_threads = True


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def log_message(self, *args):
        pass

    def setup(self):
        super().setup()
        # Disable Nagle: the classic http.server latency trap is a small
        # header segment followed by a small body segment, each waiting on
        # the client's delayed ACK (~20-40 ms per request). One segment per
        # response and no Nagle keeps a request at ~1 ms.
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    def _read_body(self):
        length = self.headers.get("Content-Length")
        if length is None:
            return b""
        try:
            n = int(length)
        except ValueError:
            return b""
        if n <= 0:
            return b""
        return self.rfile.read(n)

    def _send(self, status, ctype, body, extra=None):
        try:
            reason = self.responses.get(status, ("???",))[0]
            head = ["HTTP/1.1 %d %s\r\n" % (status, reason),
                    "Server: Forge/1.0\r\n",
                    "Content-Type: %s\r\n" % ctype,
                    "Content-Length: %d\r\n" % len(body)]
            if extra:
                for k, v in extra.items():
                    if v is not None:
                        head.append("%s: %s\r\n" % (k, v))
            head.append("\r\n")
            self.connection.sendall("".join(head).encode("latin-1") + body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _auth_ok(self):
        if not TOKEN:
            return True
        return self.headers.get("Authorization", "") == "Bearer " + TOKEN

    def _handle(self, method):
        parsed = urlparse(self.path)
        path = parsed.path
        query = parse_qs(parsed.query)
        raw = self._read_body()
        host = self.headers.get("Host", "127.0.0.1")
        try:
            with STORE_LOCK:
                status, ctype, body, extra = self._route(method, path, query, raw, host)
        except Exception as e:
            status, ctype, body, extra = _err(
                500, "%s: %s" % (type(e).__name__, e))
        extra = dict(extra or {})
        extra["X-GitHub-Request-Id"] = "req-%08d" % _next(NEXT_REQ_ID)
        self._send(status, ctype, body, extra)

    def _route(self, method, path, query, raw, host):
        if path == "/healthz":
            return (200, "application/json", _json_bytes({"ok": True}), {})
        if path.startswith("/api/v3") or path == "/api/graphql" or path == "/mcp":
            if not self._auth_ok():
                return _err(401, "Requires authentication")
            if path == "/api/graphql":
                if method != "POST":
                    return _err(405, "Method Not Allowed")
                return handle_graphql(raw)
            if path == "/mcp":
                if method != "POST":
                    return _err(405, "Method Not Allowed")
                return handle_mcp(raw)
            return handle_rest(method, path, query, raw, host)
        if ".git/" in path:
            if not self._auth_ok():
                return _err(401, "Requires authentication")
            return self._handle_git(method, path, query, raw)
        return _err(404, "Not Found")

    def _handle_git(self, method, path, query, raw):
        m = re.match(r"^/([^/]+)/([^/]+)\.git/(.+)$", path)
        if not m:
            return _err(404, "Not Found")
        owner, repo_name, tail = m.group(1), m.group(2), m.group(3)
        repo = get_repo(owner, repo_name)
        if repo is None or owner != VIEWER:
            return _err(404, "Not Found")
        if tail == "info/refs":
            service = query.get("service", [None])[0]
            if service not in ("git-upload-pack", "git-receive-pack"):
                return _err(400, "service is required")
            if method != "GET":
                return _err(405, "Method Not Allowed")
            proto = self.headers.get("Git-Protocol", "")
            if proto == "version=2":
                body = adv_v2(repo)
            else:
                body = adv_v0(repo, service)
            ctype = "application/x-%s-advertisement" % service
            return (200, ctype, body, {})
        if tail == "git-upload-pack" and method == "POST":
            proto = self.headers.get("Git-Protocol", "")
            try:
                if proto == "version=2":
                    first = raw[:4]
                    try:
                        ln = int(first, 16)
                        head = raw[4:ln] if 4 < ln <= len(raw) else b""
                    except ValueError:
                        head = b""
                    if head.startswith(b"command=ls-refs"):
                        prefixes, peel, symrefs, unborn = parse_ls_refs_request(raw)
                        body = ls_refs_body(repo, prefixes, peel, symrefs, unborn)
                    elif head.startswith(b"command=fetch"):
                        wants, haves, depth, shallow = parse_fetch_v2_request(raw)
                        body = fetch_v2_body(repo, wants, haves, depth, shallow)
                    else:
                        return _err(400, "unknown upload-pack command")
                else:
                    wants, haves, depth, shallow = parse_fetch_v0_request(raw)
                    body = fetch_v0_body(repo, wants, haves, depth, shallow)
            except ValueError as e:
                return _err(400, "malformed pkt-line: %s" % e)
            return (200, "application/x-git-upload-pack-result", body, {})
        if tail == "git-receive-pack" and method == "POST":
            body = handle_receive_pack(repo, raw)
            return (200, "application/x-git-receive-pack-result", body, {})
        return _err(404, "Not Found")

    def do_GET(self):
        self._handle("GET")

    def do_POST(self):
        self._handle("POST")

    def do_PUT(self):
        self._handle("PUT")

    def do_PATCH(self):
        self._handle("PATCH")

    def do_DELETE(self):
        self._handle("DELETE")


# ---------------------------------------------------------------- lifecycle

def _http_json(url, payload=None, timeout=10):
    data = None
    headers = {}
    method = "GET"
    if payload is not None:
        data = json.dumps(payload).encode()
        headers["Content-Type"] = "application/json"
        method = "POST"
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.status, resp.read()


def main():
    port = int(os.environ.get("MAKEFUN_LOCAL_PORT", "0"))
    server = ForgeServer(("0.0.0.0", port), ForgeHandler)
    actual_port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    if ENV_URL:
        base = ENV_URL.rstrip("/")
        registered = False
        for _ in range(20):
            try:
                status, _ = _http_json(base + "/register", {"port": actual_port})
                if status in (200, 201, 409):
                    registered = True
                    break
            except Exception:
                pass
            time.sleep(0.5)
        if not registered:
            print("failed to register with the env", file=sys.stderr)
            sys.exit(1)
        while True:
            try:
                _status, body = _http_json(base + "/done")
                if json.loads(body.decode("utf-8")).get("done") is True:
                    break
            except Exception:
                pass
            time.sleep(0.5)
        server.shutdown()
        sys.exit(0)
    print("forge listening on http://127.0.0.1:%d (local mode, no MAKEFUN_ENV_URL)"
          % actual_port, flush=True)
    try:
        while True:
            time.sleep(3600)
    except KeyboardInterrupt:
        pass
    server.shutdown()
    sys.exit(0)


if __name__ == "__main__":
    main()
