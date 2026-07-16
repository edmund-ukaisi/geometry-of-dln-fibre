"""Views: status budget, dag filtering, lookahead classification, brief monotonicity."""

from expedition_map import model, survey as sv, views
from conftest import build_map


def _small(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "R", "owner": "me",
         "title": "the goal"},
        {"id": "mid", "kind": "claim", "status": "skeleton-linked", "lean": "M",
         "owner": "cap", "title": "middle",
         "edges": [{"type": "needs", "to": "leaf"},
                   {"type": "discharges", "to": "root"}]},
        {"id": "leaf", "kind": "claim", "status": "proven", "lean": "L", "owner": "cap",
         "title": "leaf lemma", "edges": [{"type": "discharges", "to": "mid"}]},
        {"id": "rt", "kind": "route", "status": "proposed", "owner": "me",
         "title": "a strategy", "edges": [{"type": "conjectured-toward", "to": "root"}]},
    ]
    return model.load_map(build_map(tmp_path, nodes, ["root"]))


def test_status_within_budget(tmp_path):
    m = _small(tmp_path)
    text = views.render_status(m, None)
    assert len(text.splitlines()) <= 40
    assert "STATUS" in text and "live frontier" in text


def test_status_shows_open_gate_for_proposed_route(tmp_path):
    m = _small(tmp_path)
    text = views.render_status(m, None)
    assert "awaiting adoption" in text


def test_dag_filter_by_kind(tmp_path):
    m = _small(tmp_path)
    text = views.render_dag(m, kind="route")
    assert "rt" in text and "root" not in text.split("## route")[0].replace(
        "dag", "")  # root not listed as its own node under the route section
    assert "## claim" not in text


def test_lookahead_classifies(tmp_path):
    m = _small(tmp_path)
    text = views.render_lookahead(m, None)
    assert "build-time dependencies" in text
    # mid depends on leaf(proven,closed) => not build-time-blocked; root depends on
    # mid(open) => build-time-blocked.
    assert "root ⇐ mid" in text


def test_decision_view_has_cones(tmp_path):
    m = _small(tmp_path)
    text = views.render_decision(m, None, "mid")
    assert "cone up" in text and "cone down" in text
    assert "root" in text and "leaf" in text


def test_decision_unknown_node(tmp_path):
    m = _small(tmp_path)
    assert "no such node" in views.render_decision(m, None, "ghost")


def test_brief_monotone_in_size(tmp_path):
    m = _small(tmp_path)
    sizes = [views.render_brief(m, None, "mid", r)[1] for r in (1, 2, 3, 4)]
    assert sizes[0] < sizes[1] < sizes[2] < sizes[3]


def test_brief_resolution1_minimal(tmp_path):
    m = _small(tmp_path)
    text, _ = views.render_brief(m, None, "mid", 1)
    assert "ancestors" not in text        # only appears at resolution >= 2
    assert "edges:" in text


def test_brief_resolution4_has_props(tmp_path):
    m = _small(tmp_path)
    text, _ = views.render_brief(m, None, "mid", 4)
    assert "cone prop texts" in text
