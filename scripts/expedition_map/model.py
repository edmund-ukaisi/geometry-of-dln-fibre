"""Model layer: load and index an expedition map's ``claims.yaml``.

The map is a plain dict (``meta`` + ``nodes``); we keep it as dicts rather than
classes -- the schema is small and every consumer wants attribute-bag access.
This module owns the vocabulary (kinds, maturity ladders, edge types) and the
graph derivations (dependency DAG, root-reachability) that the validator and the
views join against.
"""

from __future__ import annotations

import os
import glob
from pathlib import Path

import yaml


class MapError(Exception):
    """A load/parse error with human-facing, file-anchored context."""


# ---------------------------------------------------------------------------
# Vocabulary (mirrors docs/policies/expedition-map.md)
# ---------------------------------------------------------------------------

KINDS = ("claim", "notion", "route")

# Maturity ladders, ordered low -> high.  Exit statuses live outside the ladder.
LADDERS = {
    "claim": ["conjectured", "adjudicated", "stated", "skeleton-linked", "proven"],
    "notion": ["proposed", "drafted", "validated", "frozen"],
    "route": ["proposed", "adopted", "building", "landed"],
}

# Terminal "success" statuses -- work is done, node is not open.
CLOSED_SUCCESS = {"proven", "frozen", "landed"}
# Exit statuses -- node left the plan; must carry a forwarding pointer (contract 1).
EXIT_STATUSES = {"refuted", "superseded", "retired"}

ALL_STATUSES = set(EXIT_STATUSES) | set(CLOSED_SUCCESS)
for _lad in LADDERS.values():
    ALL_STATUSES.update(_lad)

# Edge vocabulary.
DEP_EDGE_TYPES = ("needs", "discharges", "conjectured-toward", "refutes")
EXIT_EDGE_TYPES = ("forwarded-to", "superseded-by")
ALL_EDGE_TYPES = DEP_EDGE_TYPES + EXIT_EDGE_TYPES

# Selling-register lint words (contract 10 / P5).
SELLING_WORDS = ("mechanical", "just wiring", "bypasses", "trivially", "suffices")


# ---------------------------------------------------------------------------
# Status helpers
# ---------------------------------------------------------------------------

def status_rank(kind, status):
    """Index of ``status`` in its kind's ladder, or ``None`` for exit/off-ladder."""
    ladder = LADDERS.get(kind, [])
    return ladder.index(status) if status in ladder else None


def is_exit(node):
    return node.get("status") in EXIT_STATUSES


def is_closed(node):
    """Closed = terminal success or exited; carries no remaining obligation."""
    return node.get("status") in CLOSED_SUCCESS or is_exit(node)


def is_open(node):
    return not is_closed(node)


def at_least(node, status):
    """True if node's status is >= ``status`` on its own kind's ladder."""
    r = status_rank(node.get("kind"), node.get("status"))
    t = status_rank(node.get("kind"), status)
    return r is not None and t is not None and r >= t


def short_name(lean_name):
    """Last dotted component of a Lean decl name (``A.B.foo`` -> ``foo``)."""
    return lean_name.rsplit(".", 1)[-1] if lean_name else lean_name


# ---------------------------------------------------------------------------
# Map-dir resolution
# ---------------------------------------------------------------------------

def resolve_map_dir(explicit=None, start="."):
    """Resolve the map directory.

    Precedence: ``--map`` flag; ``./map``; a unique ``expeditions/*/map``.
    Raises ``MapError`` (with the candidate list) when ambiguous or absent.
    """
    if explicit:
        p = Path(explicit)
        if not p.is_dir():
            raise MapError(f"--map {explicit}: not a directory")
        return p
    local = Path(start) / "map"
    if local.is_dir():
        return local
    found = find_all_map_dirs(start)
    if len(found) == 1:
        return found[0]
    if not found:
        raise MapError(
            "no map found: pass --map <dir>, or run from a dir with ./map "
            "or expeditions/*/map"
        )
    listing = "\n  ".join(str(f) for f in found)
    raise MapError(f"multiple maps found; pass --map <dir>:\n  {listing}")


def find_all_map_dirs(start="."):
    """All ``expeditions/*/map`` dirs under ``start`` (for the pre-commit hook)."""
    pattern = os.path.join(start, "expeditions", "*", "map")
    return [Path(p) for p in sorted(glob.glob(pattern)) if Path(p, "claims.yaml").is_file()]


# ---------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------

def _normalize_node(node, path):
    """Coerce a raw node dict into the canonical shape; raise on hard errors."""
    if not isinstance(node, dict):
        raise MapError(f"{path}: node is not a mapping: {node!r}")
    nid = node.get("id")
    if not nid:
        raise MapError(f"{path}: a node is missing its `id` (near {node!r})")
    where = f"{path} [node {nid}]"
    kind = node.get("kind")
    if kind not in KINDS:
        raise MapError(f"{where}: kind must be one of {KINDS}, got {kind!r}")
    # Edges -> list of {type, to}.
    edges = node.get("edges") or []
    norm_edges = []
    for e in edges:
        if not isinstance(e, dict) or "type" not in e or "to" not in e:
            raise MapError(f"{where}: bad edge {e!r} (need {{type, to}})")
        norm_edges.append({"type": e["type"], "to": e["to"]})
    node["edges"] = norm_edges
    # Evidence -> list.
    ev = node.get("evidence") or []
    if isinstance(ev, str):
        ev = [ev]
    node["evidence"] = list(ev)
    node.setdefault("notes", "")
    node.setdefault("prop", "")
    node.setdefault("lean", "")
    node.setdefault("owner", "")
    node.setdefault("tier", "new")
    return node


def load_map(map_dir):
    """Parse ``<map_dir>/claims.yaml`` into an indexed map dict.

    Returns ``{meta, nodes, by_id, map_dir}``. Raises ``MapError`` with the
    file (and, for schema issues, the offending node id) in the message.
    """
    map_dir = Path(map_dir)
    path = map_dir / "claims.yaml"
    if not path.is_file():
        raise MapError(f"{path}: not found (is this a map directory?)")
    try:
        with open(path) as fh:
            data = yaml.safe_load(fh)
    except yaml.YAMLError as exc:
        mark = getattr(exc, "problem_mark", None)
        loc = f" (line {mark.line + 1}, col {mark.column + 1})" if mark else ""
        raise MapError(f"{path}: YAML parse error{loc}: {exc}")
    if not isinstance(data, dict):
        raise MapError(f"{path}: top level must be a mapping with meta/nodes")
    meta = data.get("meta") or {}
    if not isinstance(meta, dict):
        raise MapError(f"{path}: `meta` must be a mapping")
    raw_nodes = data.get("nodes") or []
    if not isinstance(raw_nodes, list):
        raise MapError(f"{path}: `nodes` must be a list")

    nodes = [_normalize_node(n, path) for n in raw_nodes]
    by_id = {}
    for n in nodes:
        if n["id"] in by_id:
            raise MapError(f"{path}: duplicate node id {n['id']!r}")
        by_id[n["id"]] = n
    return {"meta": meta, "nodes": nodes, "by_id": by_id, "map_dir": map_dir}


# ---------------------------------------------------------------------------
# Graph derivations
# ---------------------------------------------------------------------------

def dep_targets(node):
    """(edge_type, to) for dependency-bearing edges (excludes exit pointers)."""
    return [(e["type"], e["to"]) for e in node["edges"] if e["type"] in DEP_EDGE_TYPES]


def exit_targets(node):
    return [(e["type"], e["to"]) for e in node["edges"] if e["type"] in EXIT_EDGE_TYPES]


def build_dep_graph(m):
    """Directed dependency graph: an edge ``X -> Y`` means "X depends on Y".

    ``needs``/``conjectured-toward`` from n keep their direction (n -> to).
    ``discharges`` is *reversed*: ``n discharges t`` means t depends on n
    (n is the provider that closes t's obligation) -> edge ``t -> n``.
    ``refutes`` is orthogonal to dependency and is excluded.
    """
    adj = {n["id"]: set() for n in m["nodes"]}
    for n in m["nodes"]:
        nid = n["id"]
        for etype, to in dep_targets(n):
            if to not in adj:
                continue  # dangling ref; contract 1 reports it separately
            if etype in ("needs", "conjectured-toward"):
                adj[nid].add(to)
            elif etype == "discharges":
                adj[to].add(nid)
            # refutes: skip
    return adj


def find_cycles(adj):
    """Return one cycle (list of ids) if the directed graph has one, else []."""
    WHITE, GREY, BLACK = 0, 1, 2
    color = {v: WHITE for v in adj}
    stack = []

    def dfs(v):
        color[v] = GREY
        stack.append(v)
        for w in sorted(adj[v]):
            if color[w] == GREY:
                return stack[stack.index(w):] + [w]
            if color[w] == WHITE:
                r = dfs(w)
                if r:
                    return r
        stack.pop()
        color[v] = BLACK
        return None

    for v in sorted(adj):
        if color[v] == WHITE:
            r = dfs(v)
            if r:
                return r
    return []


def reachable_from_roots(m):
    """Ids weakly connected to a root over dependency edges.

    Liveness is undirected connectivity: a node feeds, or is fed by, the goal.
    Exit edges (forwarded-to / superseded-by) do NOT carry liveness -- a retired
    node pointing at a live successor stays dead.
    """
    adj = build_dep_graph(m)
    undirected = {v: set() for v in adj}
    for v, ws in adj.items():
        for w in ws:
            undirected[v].add(w)
            undirected[w].add(v)
    roots = [r for r in m["meta"].get("roots", []) if r in m["by_id"]]
    seen = set()
    frontier = list(roots)
    while frontier:
        v = frontier.pop()
        if v in seen:
            continue
        seen.add(v)
        frontier.extend(undirected.get(v, ()))
    return seen
