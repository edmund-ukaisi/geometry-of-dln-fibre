"""Model: loading, ladders, dependency graph, cycles, reachability, resolution."""

import pytest

from expedition_map import model
from conftest import build_map


def test_load_and_index(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "Root"},
        {"id": "a", "kind": "claim", "status": "conjectured", "owner": "me",
         "edges": [{"type": "discharges", "to": "root"}]},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["root"]))
    assert set(m["by_id"]) == {"root", "a"}
    assert m["meta"]["roots"] == ["root"]
    assert m["by_id"]["a"]["edges"][0] == {"type": "discharges", "to": "root"}


def test_duplicate_id_rejected(tmp_path):
    nodes = [{"id": "x", "kind": "claim", "status": "stated", "lean": "X"},
             {"id": "x", "kind": "notion", "status": "frozen"}]
    with pytest.raises(model.MapError, match="duplicate"):
        model.load_map(build_map(tmp_path, nodes, ["x"]))


def test_bad_kind_rejected(tmp_path):
    map_dir = tmp_path / "map"
    map_dir.mkdir()
    (map_dir / "claims.yaml").write_text(
        "meta:\n  roots: [x]\nnodes:\n  - id: x\n    kind: bogus\n    status: stated\n")
    with pytest.raises(model.MapError, match="kind"):
        model.load_map(map_dir)


def test_yaml_error_has_location(tmp_path):
    map_dir = tmp_path / "map"
    map_dir.mkdir()
    (map_dir / "claims.yaml").write_text("meta:\n  roots: [x\nnodes: [\n")
    with pytest.raises(model.MapError, match="YAML parse error"):
        model.load_map(map_dir)


def test_status_helpers():
    assert model.is_open({"kind": "claim", "status": "stated"})
    assert model.is_closed({"kind": "claim", "status": "proven"})
    assert model.is_closed({"kind": "route", "status": "refuted"})
    assert model.is_exit({"kind": "route", "status": "retired"})
    assert model.at_least({"kind": "claim", "status": "proven"}, "stated")
    assert not model.at_least({"kind": "claim", "status": "adjudicated"}, "stated")


def test_dep_graph_discharges_reversed(tmp_path):
    # a needs b; c discharges a  =>  a->b (needs) and a->c (reversed discharge).
    nodes = [
        {"id": "a", "kind": "claim", "status": "stated", "lean": "A",
         "edges": [{"type": "needs", "to": "b"}]},
        {"id": "b", "kind": "claim", "status": "proven", "lean": "B"},
        {"id": "c", "kind": "claim", "status": "proven", "lean": "C",
         "edges": [{"type": "discharges", "to": "a"}]},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["a"]))
    adj = model.build_dep_graph(m)
    assert adj["a"] == {"b", "c"}
    assert adj["c"] == set()


def test_no_false_cycle_from_redundant_needs_discharges(tmp_path):
    # box needs deeper AND deeper discharges box -> same direction, no cycle.
    nodes = [
        {"id": "box", "kind": "claim", "status": "skeleton-linked", "lean": "Box",
         "owner": "me", "edges": [{"type": "needs", "to": "deeper"}]},
        {"id": "deeper", "kind": "claim", "status": "stated", "lean": "Deep",
         "owner": "me", "edges": [{"type": "discharges", "to": "box"}]},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["box"]))
    assert model.find_cycles(model.build_dep_graph(m)) == []


def test_real_cycle_detected(tmp_path):
    nodes = [
        {"id": "a", "kind": "claim", "status": "stated", "lean": "A", "owner": "me",
         "edges": [{"type": "needs", "to": "b"}]},
        {"id": "b", "kind": "claim", "status": "stated", "lean": "B", "owner": "me",
         "edges": [{"type": "needs", "to": "a"}]},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["a"]))
    assert model.find_cycles(model.build_dep_graph(m))


def test_reachability(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "near", "kind": "claim", "status": "stated", "lean": "N", "owner": "me",
         "edges": [{"type": "discharges", "to": "root"}]},
        {"id": "island", "kind": "claim", "status": "conjectured", "owner": "me"},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["root"]))
    reach = model.reachable_from_roots(m)
    assert "near" in reach and "root" in reach and "island" not in reach


def test_resolve_map_dir_explicit_and_missing(tmp_path):
    md = build_map(tmp_path, [{"id": "x", "kind": "claim", "status": "stated",
                               "lean": "X"}], ["x"])
    assert model.resolve_map_dir(str(md)) == md
    with pytest.raises(model.MapError):
        model.resolve_map_dir(str(tmp_path / "nope"))
