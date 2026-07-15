"""Guarded operations: rename, tombstone, new, calibration, anchors.

These are the edits the spec marks as error-prone by hand, so the CLI is
authoritative. rename/tombstone edit ``claims.yaml`` with a *line editor* (not a
parse-and-redump) so authored comments and ordering survive; both re-parse the
result to guarantee a well-formed map before returning.
"""

from __future__ import annotations

import re
import datetime
from pathlib import Path

from . import model


def _now():
    return datetime.date.today().isoformat()


# ---------------------------------------------------------------------------
# claims.yaml line editing
# ---------------------------------------------------------------------------

def _token_re(tok):
    return re.compile(r"(?<![\w-])" + re.escape(tok) + r"(?![\w-])")


def _rewrite_id_in_text(text, old, new):
    """Replace whole-token ``old`` -> ``new`` only in structural id positions:
    ``id:`` values, ``to:`` values, and ``roots`` (flow or block). Prose fields
    (title/notes/prop/…) are left untouched.
    """
    tok = _token_re(old)
    out = []
    in_roots_block = False
    for line in text.splitlines():
        stripped = line.lstrip()
        indent = len(line) - len(stripped)
        structural = False
        if re.match(r"-?\s*id:\s", stripped):
            structural = True
        if "to:" in stripped:
            structural = True
        if re.match(r"roots:", stripped):
            structural = True
            # Flow list on the same line, or a following block list.
            in_roots_block = "[" not in line
        elif in_roots_block:
            if stripped.startswith("-") and indent > 0:
                structural = True
            else:
                in_roots_block = False
        if structural:
            line = tok.sub(new, line)
        out.append(line)
    tail = "\n" if text.endswith("\n") else ""
    return "\n".join(out) + tail


def _node_span(lines, nid):
    """Return (start, end) line indices for the block-list node with ``id: nid``.

    Recognizes ``- id: <nid>`` (list-item form). The block runs until the next
    list item at the same indent, a top-level key, or EOF.
    """
    start = None
    start_indent = 0
    pat = re.compile(r"^(\s*)-\s+id:\s*" + re.escape(nid) + r"\s*$")
    for i, line in enumerate(lines):
        mobj = pat.match(line)
        if mobj:
            start = i
            start_indent = len(mobj.group(1))
            break
    if start is None:
        return None
    for j in range(start + 1, len(lines)):
        line = lines[j]
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        is_item = re.match(r"^\s*-\s+id:\s", line)
        if indent <= start_indent and (is_item or indent == 0):
            return (start, j)
    return (start, len(lines))


def rename(map_dir, old, new):
    """Rename a node id everywhere; leave a forwarding pointer in naming.md."""
    map_dir = Path(map_dir)
    path = map_dir / "claims.yaml"
    m = model.load_map(map_dir)
    if old not in m["by_id"]:
        raise model.MapError(f"rename: no node with id {old!r}")
    if new in m["by_id"]:
        raise model.MapError(f"rename: id {new!r} already exists")
    text = path.read_text()
    path.write_text(_rewrite_id_in_text(text, old, new))
    # Re-parse: guarantee well-formed and that the rename landed.
    m2 = model.load_map(map_dir)
    if new not in m2["by_id"] or old in m2["by_id"]:
        raise model.MapError(f"rename: post-edit map inconsistent (old={old} new={new})")
    _append_naming(map_dir, old, new)
    return ("renamed. Anchors are now stale — run `expedition anchors emit` and "
            "recompile the green-gate to re-pin.")


def _append_naming(map_dir, old, new, reason="rename"):
    p = Path(map_dir) / "overlay" / "naming.md"
    p.parent.mkdir(parents=True, exist_ok=True)
    header = "# Naming forwarding-pointers\n\n"
    if not p.is_file():
        p.write_text(header)
    line = f"- `{old}` → `{new}`  ({reason}, {_now()})\n"
    with open(p, "a") as fh:
        fh.write(line)


def tombstone(map_dir, nid, forward, reason):
    """Retire a node: status -> retired, add a forwarded-to edge, overlay note."""
    map_dir = Path(map_dir)
    path = map_dir / "claims.yaml"
    m = model.load_map(map_dir)
    if nid not in m["by_id"]:
        raise model.MapError(f"tombstone: no node with id {nid!r}")
    if forward not in m["by_id"]:
        raise model.MapError(f"tombstone: forward target {forward!r} is not a node")
    lines = path.read_text().splitlines()
    span = _node_span(lines, nid)
    if span is None:
        raise model.MapError(
            f"tombstone: could not locate `- id: {nid}` block (is it block-list form?)")
    start, end = span
    start_indent = len(lines[start]) - len(lines[start].lstrip())
    block = lines[start:end]
    field_indent = None
    edges_idx = None
    last_field = 0
    for k, line in enumerate(block):
        s = line.lstrip()
        ind = len(line) - len(s)
        if line.strip() and ind > start_indent:
            last_field = k  # a real field of this node (not a trailing comment)
        if field_indent is None and re.match(r"[a-z_]+:", s) and not s.startswith("-"):
            field_indent = ind
        if re.match(r"status:", s):
            block[k] = " " * ind + "status: retired"
        if re.match(r"edges:", s):
            edges_idx = k
    field_indent = field_indent if field_indent is not None else start_indent + 2
    edge_line = " " * (field_indent + 2) + \
        f"- {{type: forwarded-to, to: {forward}}}"
    if edges_idx is not None:
        block.insert(edges_idx + 1, edge_line)
    else:
        # Insert right after the last real field, before any trailing blank/comment.
        block[last_field + 1:last_field + 1] = [
            " " * field_indent + "edges:", edge_line]
    lines[start:end] = block
    path.write_text("\n".join(lines) + "\n")
    m2 = model.load_map(map_dir)   # re-parse guard
    node = m2["by_id"][nid]
    assert node["status"] == "retired"
    _append_naming(map_dir, nid, forward, reason="tombstone")
    _append_dead_route(map_dir, nid, reason, forward)
    return f"tombstoned {nid} -> {forward}. Retire its skeleton hole in this commit."


def _append_dead_route(map_dir, nid, reason, forward):
    p = Path(map_dir) / "overlay" / "dead-routes.md"
    p.parent.mkdir(parents=True, exist_ok=True)
    if not p.is_file():
        p.write_text("# Dead-route registry\n\n")
    with open(p, "a") as fh:
        fh.write(f"- `{nid}` — {reason} (→ `{forward}`, {_now()})\n")


# ---------------------------------------------------------------------------
# new (scaffold, printed not inserted)
# ---------------------------------------------------------------------------

SCAFFOLD = {
    "claim": """  - id: {id}
    kind: claim
    title: "TODO ≤80 chars — names what is PROVEN-or-claimed"
    prop: |
      TODO statement (verbatim math / Lean-adjacent)
    lean: ""            # decl name once `stated`
    status: conjectured
    tier: new
    owner: ""           # thread/seat, or 'parked: <reason>'
    kill: ""            # battery/<name>.py
    edges:
      - {{type: needs, to: TODO}}
    evidence: []
    notes: ""
""",
    "notion": """  - id: {id}
    kind: notion
    title: "TODO — the carrier whose shape is the design question"
    status: proposed
    owner: ""
    notes: ""
""",
    "route": """  - id: {id}
    kind: route
    title: "TODO — the decomposition strategy"
    status: proposed
    owner: ""
    kill: ""
    edges:
      - {{type: needs, to: TODO}}
    evidence: []
    notes: ""
""",
}


def scaffold(kind, nid):
    if kind not in SCAFFOLD:
        raise model.MapError(f"new: kind must be one of {tuple(SCAFFOLD)}")
    body = SCAFFOLD[kind].format(id=nid)
    return (f"# paste under `nodes:` in claims.yaml (NOT auto-inserted)\n{body}")


# ---------------------------------------------------------------------------
# calibration ledger
# ---------------------------------------------------------------------------

def _calib_path(map_dir):
    return Path(map_dir) / "calibration.md"


def calibration_add(map_dir, node, predicted, actual):
    p = _calib_path(map_dir)
    if not p.is_file():
        p.write_text("# Calibration ledger\n\n"
                     "| date | node | predicted | actual |\n"
                     "|---|---|---|---|\n")
    with open(p, "a") as fh:
        fh.write(f"| {_now()} | {node} | {predicted} | {actual} |\n")
    return f"logged calibration for {node}"


def _lead_num(s):
    m = re.search(r"-?\d+(?:\.\d+)?", s or "")
    return float(m.group()) if m else None


def calibration_show(map_dir):
    p = _calib_path(map_dir)
    if not p.is_file():
        return "no calibration ledger yet (use `calibration add`)"
    rows = []
    for line in p.read_text().splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) != 4 or cells[0] in ("date", "---"):
            continue
        rows.append(cells)
    n = len(rows)
    matched = over = under = na = 0
    for _, _, pred, act in rows:
        pn, an = _lead_num(pred), _lead_num(act)
        if pn is not None and an is not None:
            if an == pn:
                matched += 1
            elif an > pn:
                under += 1   # actual exceeded prediction -> under-estimated
            else:
                over += 1
        elif pred == act:
            matched += 1
        else:
            na += 1
    return (f"calibration: {n} rows | matched={matched} "
            f"over-estimated={over} under-estimated={under} unscored={na}")


# ---------------------------------------------------------------------------
# anchors emit
# ---------------------------------------------------------------------------

def anchors_emit(m, out=None):
    """Emit a MapAnchors.lean skeleton of ``#check`` pins.

    v0 honesty: a real ``example : <prop> := <name>`` needs hand-translation of
    prose props, so we emit ``#check @<name>`` pins plus a TODO for the full
    statement pin. Only nodes with both ``lean`` and ``prop`` are pinned.
    """
    lines = [
        "-- AUTOGENERATED by `expedition anchors emit`. Do not edit by hand.",
        "-- v0: these are #check pins, NOT full statement pins. A statement pin",
        "--     `example : <prop> := <name>` needs hand-translation of the prose",
        "--     prop; see the TODO under each node.",
        "import DLNFibre",
        "",
        "namespace MapAnchors",
        "",
    ]
    npinned = 0
    for n in m["nodes"]:
        if not (n.get("lean") and n.get("prop")):
            continue
        npinned += 1
        first = next((ln for ln in str(n["prop"]).splitlines() if ln.strip()), "")
        lines.append(f"-- map: {n['id']}")
        lines.append(f"-- prop: {first.strip()}")
        lines.append(f"#check @{n['lean']}")
        lines.append(f"-- TODO statement pin: example : «{n['id']}» := {n['lean']}")
        lines.append("")
    lines.append("end MapAnchors")
    text = "\n".join(lines) + "\n"
    if out:
        Path(out).write_text(text)
    return text, npinned
