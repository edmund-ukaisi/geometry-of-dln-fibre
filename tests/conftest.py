"""Shared test helpers.

Puts ``scripts/`` on the path so ``import expedition_map`` works, and provides a
canonical-format ``claims.yaml`` writer (block-list nodes, flow-style edges) that
matches the hand-authored production format -- so rename/tombstone tests exercise
the same line shapes the real controller writes.
"""

import os
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

REAL_FIXTURE = Path(__file__).resolve().parent / "fixtures" / "aoyagi-endgame"
CONE_JSON = REPO / "docs" / "retro" / "aoyagi-full" / "substrate" / "cone_before_mint.json"


def _fmt_edges(edges, indent):
    out = [f"{' ' * indent}edges:"]
    for e in edges:
        out.append(f"{' ' * (indent + 2)}- {{type: {e['type']}, to: {e['to']}}}")
    return out


def dump_claims(nodes, roots, expedition="test", updated="2026-07-15"):
    """Serialize a map to canonical claims.yaml text."""
    lines = [
        "meta:",
        f"  expedition: {expedition}",
        f"  roots: [{', '.join(roots)}]",
        f"  updated: {updated}",
        "nodes:",
    ]
    for n in nodes:
        lines.append(f"  - id: {n['id']}")
        for key in ("kind", "title", "lean", "status", "tier", "owner", "kill"):
            if key in n and n[key] not in (None, ""):
                val = n[key]
                if key in ("title", "notes", "owner") and (
                        ":" in str(val) or '"' in str(val)):
                    val = '"' + str(val).replace('"', "'") + '"'
                lines.append(f"    {key}: {val}")
        if n.get("prop"):
            lines.append("    prop: |")
            for pl in str(n["prop"]).rstrip().splitlines():
                lines.append(f"      {pl}")
        if n.get("edges"):
            lines.extend(_fmt_edges(n["edges"], 4))
        if n.get("evidence"):
            ev = ", ".join(n["evidence"])
            lines.append(f"    evidence: [{ev}]")
        if n.get("notes"):
            note = str(n["notes"]).replace('"', "'")
            lines.append(f'    notes: "{note}"')
    return "\n".join(lines) + "\n"


def build_map(tmp_path, nodes, roots, **kw):
    """Write a map dir under ``tmp_path`` and return its Path."""
    map_dir = tmp_path / "map"
    map_dir.mkdir(parents=True, exist_ok=True)
    (map_dir / "claims.yaml").write_text(dump_claims(nodes, roots, **kw))
    return map_dir


@pytest.fixture
def real_fixture():
    return REAL_FIXTURE / "map"


@pytest.fixture
def real_fixture_survey(real_fixture, tmp_path):
    """A copy of the real fixture with a cone-mode survey built from cone_before_mint."""
    import shutil, json
    from expedition_map import model, survey as sv
    dst = tmp_path / "aoyagi" / "map"
    shutil.copytree(real_fixture, dst)
    m = model.load_map(dst)
    data = json.load(open(CONE_JSON))
    survey = sv.build_survey(m, data, str(CONE_JSON))
    sv.write_survey(m, survey)
    return dst
