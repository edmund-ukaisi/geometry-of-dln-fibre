"""Landmarks (§ Landmarks): cap, stale-landmark, and the view surfaces."""

from expedition_map import model, validate as V, views
from conftest import build_map


def _run(map_dir, fast=True):
    m = model.load_map(map_dir)
    return m, V.validate(m, None, fast=fast)


def _c11(findings):
    return [f for f in findings if f.contract == 11]


def _has_error(findings, c):
    return any(f.contract == c and f.level == "error" for f in findings)


def test_landmark_field_defaults_false(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"}]
    m = model.load_map(build_map(tmp_path, nodes, ["r"]))
    assert m["by_id"]["r"]["landmark"] is False
    assert model.landmarks(m) == []


def test_landmark_within_cap_ok(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "R",
              "owner": "me", "landmark": True}]
    _, findings = _run(build_map(tmp_path, nodes, ["r"]))
    assert not _has_error(findings, 11)


def test_landmark_cap_exceeded_errors_and_names_all(tmp_path):
    # 10 landmarks -> over the cap of 9.
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"}]
    for i in range(10):
        nodes.append({"id": f"lm{i}", "kind": "claim", "status": "conjectured",
                      "owner": "me", "landmark": True,
                      "edges": [{"type": "discharges", "to": "r"}]})
    m, findings = _run(build_map(tmp_path, nodes, ["r"]))
    errs = [f for f in _c11(findings) if f.level == "error"]
    assert len(errs) == 1
    msg = errs[0].message
    assert "10 landmarks" in msg and "cap of 9" in msg
    for i in range(10):
        assert f"lm{i}" in msg  # names all, so demotion is easy


def test_stale_landmark_warns(tmp_path):
    nodes = [
        {"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "dead", "kind": "route", "status": "refuted", "owner": "parked: x",
         "landmark": True, "edges": [{"type": "forwarded-to", "to": "r"}]},
    ]
    m, findings = _run(build_map(tmp_path, nodes, ["r"]))
    warns = [f for f in _c11(findings) if f.level == "warning"]
    assert any(w.node == "dead" and "stale landmark" in w.message for w in warns)


def test_live_landmark_not_stale(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "proven", "lean": "R",
              "owner": "me", "landmark": True}]
    m, findings = _run(build_map(tmp_path, nodes, ["r"]))
    assert not any(f.contract == 11 and f.level == "warning" for f in findings)


def _landmark_map(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "R", "owner": "me",
         "title": "goal", "landmark": True},
        {"id": "mid", "kind": "claim", "status": "skeleton-linked", "lean": "M",
         "owner": "me", "title": "middle",
         "edges": [{"type": "needs", "to": "leaf"},
                   {"type": "discharges", "to": "root"}]},
        {"id": "leaf", "kind": "claim", "status": "proven", "lean": "L", "owner": "me",
         "title": "leaf", "landmark": True,
         "edges": [{"type": "discharges", "to": "mid"}]},
    ]
    return model.load_map(build_map(tmp_path, nodes, ["root"]))


def test_status_opens_with_landmarks(tmp_path):
    m = _landmark_map(tmp_path)
    text = views.render_status(m, None)
    lines = text.splitlines()
    # landmarks section comes before the roots section.
    assert "## landmarks" in text
    assert lines.index("## landmarks") < lines.index(
        next(l for l in lines if l.startswith("## roots")))
    assert len(lines) <= 40


def test_status_budget_with_many_landmarks(tmp_path):
    # 9 landmarks + many frontier nodes must still fit in 40 lines.
    nodes = [{"id": "root", "kind": "claim", "status": "stated", "lean": "R",
              "owner": "me", "landmark": True}]
    for i in range(8):
        nodes.append({"id": f"lm{i}", "kind": "claim", "status": "conjectured",
                      "owner": "me", "landmark": True,
                      "edges": [{"type": "discharges", "to": "root"}]})
    for i in range(20):
        nodes.append({"id": f"f{i}", "kind": "claim", "status": "conjectured",
                      "owner": "me", "edges": [{"type": "discharges", "to": "root"}]})
    m = model.load_map(build_map(tmp_path, nodes, ["root"]))
    text = views.render_status(m, None)
    assert len(text.splitlines()) <= 40
    assert "more" in text  # frontier was compressed


def test_brief_r2_has_landmark_orientation(tmp_path):
    m = _landmark_map(tmp_path)
    text, _ = views.render_brief(m, None, "mid", 2)
    assert "## landmarks (orientation)" in text
    assert "ancestor (this feeds it)" in text   # root consumes mid
    assert "descendant (feeds this)" in text    # mid rests on leaf


def test_brief_r1_no_landmark_section(tmp_path):
    m = _landmark_map(tmp_path)
    text, _ = views.render_brief(m, None, "mid", 1)
    assert "landmarks" not in text.lower()


def test_dag_landmarks_filter(tmp_path):
    m = _landmark_map(tmp_path)
    text = views.render_dag(m, landmarks_only=True)
    assert "landmarks only" in text
    assert "root" in text and "leaf" in text
    assert "mid" not in text                    # mid is not a landmark


def test_decision_shows_relation_to_landmarks(tmp_path):
    m = _landmark_map(tmp_path)
    text = views.render_decision(m, None, "mid")
    assert "## relation to landmarks" in text
    assert "root" in text and "leaf" in text
