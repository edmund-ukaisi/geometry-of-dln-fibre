"""Guarded ops: rename, tombstone, new scaffold, calibration, anchors."""

import pytest

from expedition_map import model, ops
from conftest import build_map


def _mk(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "skeleton-linked", "lean": "Root",
         "owner": "me", "prop": "root prop",
         "edges": [{"type": "needs", "to": "child"}]},
        {"id": "child", "kind": "claim", "status": "stated", "lean": "Child",
         "owner": "me", "prop": "child prop",
         "edges": [{"type": "discharges", "to": "root"}]},
    ]
    return build_map(tmp_path, nodes, ["root"])


def test_rename_rewrites_all_references(tmp_path):
    md = _mk(tmp_path)
    ops.rename(md, "child", "kid")
    m = model.load_map(md)
    assert "kid" in m["by_id"] and "child" not in m["by_id"]
    # root's needs edge now points at kid.
    assert any(e["to"] == "kid" for e in m["by_id"]["root"]["edges"])
    naming = (md / "overlay" / "naming.md").read_text()
    assert "`child` → `kid`" in naming


def test_rename_root_updates_meta(tmp_path):
    md = _mk(tmp_path)
    ops.rename(md, "root", "goal")
    m = model.load_map(md)
    assert m["meta"]["roots"] == ["goal"]


def test_rename_unknown_and_collision(tmp_path):
    md = _mk(tmp_path)
    with pytest.raises(model.MapError):
        ops.rename(md, "nope", "x")
    with pytest.raises(model.MapError):
        ops.rename(md, "child", "root")


def test_rename_leaves_prose_untouched(tmp_path):
    # 'child' appears as a token in a title/notes; rename must not touch prose.
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "R", "owner": "me",
         "notes": "the child of this is elsewhere"},
        {"id": "child", "kind": "claim", "status": "stated", "lean": "C", "owner": "me",
         "edges": [{"type": "discharges", "to": "root"}]},
    ]
    md = build_map(tmp_path, nodes, ["root"])
    ops.rename(md, "child", "kid")
    text = (md / "claims.yaml").read_text()
    assert "the child of this is elsewhere" in text  # prose survives


def test_tombstone_roundtrip(tmp_path):
    md = _mk(tmp_path)
    ops.tombstone(md, "child", "root", "superseded by direct route")
    m = model.load_map(md)
    node = m["by_id"]["child"]
    assert node["status"] == "retired"
    assert any(e == {"type": "forwarded-to", "to": "root"} for e in node["edges"])
    dead = (md / "overlay" / "dead-routes.md").read_text()
    assert "child" in dead and "superseded by direct route" in dead


def test_tombstone_appends_to_existing_edges(tmp_path):
    md = _mk(tmp_path)
    ops.tombstone(md, "child", "root", "reason")
    # child already had a discharges edge; both should be present.
    m = model.load_map(md)
    types = {e["type"] for e in m["by_id"]["child"]["edges"]}
    assert {"discharges", "forwarded-to"} <= types


def test_tombstone_bad_target(tmp_path):
    md = _mk(tmp_path)
    with pytest.raises(model.MapError):
        ops.tombstone(md, "child", "ghost", "reason")


def test_new_scaffold_contains_id_and_kind(tmp_path):
    for kind in ("claim", "notion", "route"):
        s = ops.scaffold(kind, f"my-{kind}")
        assert f"id: my-{kind}" in s
        assert f"kind: {kind}" in s


def test_new_scaffold_bad_kind():
    with pytest.raises(model.MapError):
        ops.scaffold("bogus", "x")


def test_calibration_add_and_show(tmp_path):
    md = _mk(tmp_path)
    ops.calibration_add(md, "child", "3 days", "5 days")
    ops.calibration_add(md, "root", "2", "2")
    summary = ops.calibration_show(md)
    assert "2 rows" in summary
    assert "matched=1" in summary        # root 2==2
    assert "under-estimated=1" in summary  # child actual 5 > predicted 3


def test_calibration_show_empty(tmp_path):
    md = _mk(tmp_path)
    assert "no calibration" in ops.calibration_show(md)


def test_anchors_emit_check_pins(tmp_path):
    md = _mk(tmp_path)
    m = model.load_map(md)
    text, n = ops.anchors_emit(m)
    assert n == 2  # both nodes have lean + prop
    assert "#check @Root" in text and "#check @Child" in text
    assert "-- map: root" in text
    assert "TODO statement pin" in text  # v0 honesty


def test_anchors_emit_to_file(tmp_path):
    md = _mk(tmp_path)
    m = model.load_map(md)
    out = tmp_path / "MapAnchors.lean"
    ops.anchors_emit(m, out=str(out))
    assert out.is_file() and "#check @Root" in out.read_text()
