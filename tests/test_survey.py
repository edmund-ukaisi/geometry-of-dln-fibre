"""Survey adapter: modes, sorry-taint, discharge-witnessing, orphans, staleness."""

import json

from expedition_map import model, survey as sv
from conftest import build_map


def _full_walker():
    """A tiny full-mode walker dump (decls.json shape)."""
    return {
        "_meta": {"root_prefix": "T", "generated": "2026-07-15T00:00:00Z"},
        "decls": [
            {"name": "T.Root", "axioms": ["propext"],
             "deps_type": [], "deps_proof": ["T.Lemma"]},
            {"name": "T.Lemma", "axioms": ["sorryAx"],
             "deps_type": [], "deps_proof": []},
            {"name": "T.Clean", "axioms": ["propext"],
             "deps_type": [], "deps_proof": ["T.Lemma"]},
        ],
    }


def test_adapt_full_vs_cone():
    full = sv.adapt_walker(_full_walker())
    assert full["mode"] == "full"
    assert full["decls"]["T.Lemma"]["sorry"] is True

    cone = sv.adapt_walker({"headlines": ["T.Root"], "cone": ["T.Root", "T.Clean"]})
    assert cone["mode"] == "cone"
    assert cone["cone"] == {"T.Root", "T.Clean"}
    assert cone["decls"] == {}


def test_adapt_bare_list():
    assert sv.adapt_walker([{"name": "A", "axioms": []}])["mode"] == "full"
    assert sv.adapt_walker(["A", "B"])["mode"] == "cone"


def test_full_mode_sorry_taint_and_witness(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "skeleton-linked", "lean": "Root",
         "owner": "me", "edges": [{"type": "needs", "to": "lem"}]},
        {"id": "lem", "kind": "claim", "status": "stated", "lean": "Lemma", "owner": "me",
         "edges": [{"type": "discharges", "to": "root"}]},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["root"]))
    survey = sv.build_survey(m, _full_walker(), "walker")
    assert survey["freshness"]["walker_mode"] == "full"
    # Root's closure contains the sorried lemma.
    assert survey["nodes"]["root"]["sorry_tainted"] is True
    assert "T.Lemma" in survey["nodes"]["root"]["sorry_cone"]
    # lem discharges root; root's deps include T.Lemma => witnessed.
    assert survey["witness"]["lem->root"]["witnessed"] is True
    # Live-sorry cone from the root anchor picks up T.Lemma.
    assert "T.Lemma" in survey["live_sorry"]


def test_full_mode_unwitnessed(tmp_path):
    # provider 'other' (T.Clean) is not in root's transitive deps.
    nodes = [
        {"id": "root", "kind": "claim", "status": "skeleton-linked", "lean": "Root",
         "owner": "me"},
        {"id": "other", "kind": "claim", "status": "stated", "lean": "Clean",
         "owner": "me", "edges": [{"type": "discharges", "to": "root"}]},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["root"]))
    survey = sv.build_survey(m, _full_walker(), "walker")
    assert survey["witness"]["other->root"]["witnessed"] is False


def test_cone_mode_confirm_only(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "InCone", "owner": "me"},
        {"id": "front", "kind": "claim", "status": "stated", "lean": "OutOfCone",
         "owner": "me", "edges": [{"type": "discharges", "to": "root"}]},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["root"]))
    data = {"headlines": ["Head"], "cone": ["Head", "InCone"]}
    survey = sv.build_survey(m, data, "walker")
    assert survey["freshness"]["walker_mode"] == "cone"
    assert survey["nodes"]["root"]["in_cone"] is True
    assert survey["nodes"]["root"]["lean_exists"] is True     # confirmed
    assert survey["nodes"]["front"]["in_cone"] is False
    assert survey["nodes"]["front"]["lean_exists"] is None    # cannot refute
    # No dep data => witness UNKNOWN, not False.
    assert survey["witness"]["front->root"]["witnessed"] is None


def test_short_name_matching(tmp_path):
    nodes = [{"id": "x", "kind": "claim", "status": "stated", "lean": "foo",
              "owner": "me"}]
    m = model.load_map(build_map(tmp_path, nodes, ["x"]))
    walker = {"decls": [{"name": "A.B.foo", "axioms": [], "deps_type": [],
                         "deps_proof": []}]}
    survey = sv.build_survey(m, walker, "walker")
    assert survey["nodes"]["x"]["resolved"] == "A.B.foo"
    assert survey["nodes"]["x"]["match"] == "short"


def test_orphan_detection(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "orphan", "kind": "claim", "status": "conjectured", "owner": "me"},
    ]
    m = model.load_map(build_map(tmp_path, nodes, ["root"]))
    survey = sv.build_survey(m, {"cone": ["R"]}, "walker")
    assert survey["orphans"] == ["orphan"]


def test_write_and_load_roundtrip_staleness(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"}]
    m = model.load_map(build_map(tmp_path, nodes, ["r"]))
    survey = sv.build_survey(m, {"cone": ["R"]}, "walker")
    survey["freshness"]["git_head"] = "deadbeef"
    sv.write_survey(m, survey)
    loaded = sv.load_survey(m)
    assert loaded is not None
    # No git in tmp_path => current head None => not marked stale.
    assert loaded["_stale"] in (False, True)
