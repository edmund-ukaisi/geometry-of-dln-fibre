"""Validator: every contract has a passing AND a failing case."""

from expedition_map import model, survey as sv, validate as V
from conftest import build_map


def _run(map_dir, walker=None, fast=False):
    m = model.load_map(map_dir)
    survey = sv.build_survey(m, walker, "walker") if walker else None
    return V.validate(m, survey, fast=fast)


def _by_c(findings, c):
    return [f for f in findings if f.contract == c]


def _has_error(findings, c):
    return any(f.contract == c and f.level == "error" for f in findings)


# --- Contract 1 -----------------------------------------------------------

def test_c1_pass(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"}]
    assert not _has_error(_run(build_map(tmp_path, nodes, ["r"])), 1)


def test_c1_dangling_edge(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me",
              "edges": [{"type": "needs", "to": "ghost"}]}]
    assert _has_error(_run(build_map(tmp_path, nodes, ["r"])), 1)


def test_c1_exit_needs_forwarding(tmp_path):
    nodes = [
        {"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "dead", "kind": "route", "status": "refuted", "owner": "parked: x"},
    ]
    assert _has_error(_run(build_map(tmp_path, nodes, ["r"])), 1)


def test_c1_exit_with_forwarding_ok(tmp_path):
    nodes = [
        {"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "dead", "kind": "route", "status": "refuted", "owner": "parked: x",
         "edges": [{"type": "forwarded-to", "to": "r"}]},
    ]
    assert not _has_error(_run(build_map(tmp_path, nodes, ["r"])), 1)


# --- Contract 2 -----------------------------------------------------------

def test_c2_missing_lean_on_stated_warns(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "owner": "me"}]
    fs = _by_c(_run(build_map(tmp_path, nodes, ["r"]), fast=True), 2)
    assert any(f.level == "warning" for f in fs)


def test_c2_full_mode_absent_is_error(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "Ghost",
              "owner": "me"}]
    walker = {"decls": [{"name": "T.Real", "axioms": [], "deps_type": [],
                         "deps_proof": []}]}
    assert _has_error(_run(build_map(tmp_path, nodes, ["r"]), walker), 2)


def test_c2_full_mode_present_ok(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "Real",
              "owner": "me"}]
    walker = {"decls": [{"name": "T.Real", "axioms": [], "deps_type": [],
                         "deps_proof": []}]}
    assert not _has_error(_run(build_map(tmp_path, nodes, ["r"]), walker), 2)


# --- Contract 3 -----------------------------------------------------------

def test_c3_proven_sorry_tainted_is_error(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "proven", "lean": "Root",
              "owner": "me"}]
    walker = {"decls": [
        {"name": "T.Root", "axioms": ["sorryAx"], "deps_type": [], "deps_proof": []}]}
    assert _has_error(_run(build_map(tmp_path, nodes, ["r"]), walker), 3)


def test_c3_proven_clean_ok(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "proven", "lean": "Root",
              "owner": "me"}]
    walker = {"decls": [
        {"name": "T.Root", "axioms": ["propext"], "deps_type": [], "deps_proof": []}]}
    assert not _has_error(_run(build_map(tmp_path, nodes, ["r"]), walker), 3)


# --- Contract 4 -----------------------------------------------------------

def test_c4_unwitnessed_full_mode_error(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "skeleton-linked", "lean": "Root",
         "owner": "me"},
        {"id": "prov", "kind": "claim", "status": "stated", "lean": "Clean",
         "owner": "me", "edges": [{"type": "discharges", "to": "root"}]},
    ]
    walker = {"decls": [
        {"name": "T.Root", "axioms": [], "deps_type": [], "deps_proof": []},
        {"name": "T.Clean", "axioms": [], "deps_type": [], "deps_proof": []}]}
    assert _has_error(_run(build_map(tmp_path, nodes, ["root"]), walker), 4)


def test_c4_witnessed_ok(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "skeleton-linked", "lean": "Root",
         "owner": "me"},
        {"id": "prov", "kind": "claim", "status": "stated", "lean": "Lemma",
         "owner": "me", "edges": [{"type": "discharges", "to": "root"}]},
    ]
    walker = {"decls": [
        {"name": "T.Root", "axioms": [], "deps_type": [], "deps_proof": ["T.Lemma"]},
        {"name": "T.Lemma", "axioms": [], "deps_type": [], "deps_proof": []}]}
    assert not _has_error(_run(build_map(tmp_path, nodes, ["root"]), walker), 4)


# --- Contract 5 -----------------------------------------------------------

def test_c5_unmapped_live_sorry_is_error(tmp_path):
    # Root anchors T.Root whose closure sorries via T.Hidden (no node maps it).
    nodes = [{"id": "root", "kind": "claim", "status": "stated", "lean": "Root",
              "owner": "me"}]
    walker = {"decls": [
        {"name": "T.Root", "axioms": [], "deps_type": [], "deps_proof": ["T.Hidden"]},
        {"name": "T.Hidden", "axioms": ["sorryAx"], "deps_type": [], "deps_proof": []}]}
    assert _has_error(_run(build_map(tmp_path, nodes, ["root"]), walker), 5)


def test_c5_mapped_live_sorry_ok(tmp_path):
    # The sorried dep IS anchored by a node => registered => no C5 error.
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "Root", "owner": "me",
         "edges": [{"type": "needs", "to": "hid"}]},
        {"id": "hid", "kind": "claim", "status": "stated", "lean": "Hidden", "owner": "me",
         "edges": [{"type": "discharges", "to": "root"}]},
    ]
    walker = {"decls": [
        {"name": "T.Root", "axioms": [], "deps_type": [], "deps_proof": ["T.Hidden"]},
        {"name": "T.Hidden", "axioms": ["sorryAx"], "deps_type": [], "deps_proof": []}]}
    assert not _has_error(_run(build_map(tmp_path, nodes, ["root"]), walker), 5)


# --- Contract 6 -----------------------------------------------------------

def test_c6_open_without_owner_error(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "stated", "lean": "R"}]
    assert _has_error(_run(build_map(tmp_path, nodes, ["r"]), fast=True), 6)


def test_c6_closed_without_owner_ok(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "proven", "lean": "R"}]
    assert not _has_error(_run(build_map(tmp_path, nodes, ["r"]), fast=True), 6)


# --- Contract 7 -----------------------------------------------------------

def test_c7_immature_notion_error(tmp_path):
    nodes = [
        {"id": "c", "kind": "claim", "status": "stated", "lean": "C", "owner": "me",
         "edges": [{"type": "needs", "to": "n"}]},
        {"id": "n", "kind": "notion", "status": "drafted", "owner": "me"},
    ]
    assert _has_error(_run(build_map(tmp_path, nodes, ["c"]), fast=True), 7)


def test_c7_frozen_notion_ok(tmp_path):
    nodes = [
        {"id": "c", "kind": "claim", "status": "stated", "lean": "C", "owner": "me",
         "edges": [{"type": "needs", "to": "n"}]},
        {"id": "n", "kind": "notion", "status": "frozen", "owner": "me"},
    ]
    assert not _has_error(_run(build_map(tmp_path, nodes, ["c"]), fast=True), 7)


# --- Contract 8 -----------------------------------------------------------

def test_c8_orphan_open_error(tmp_path):
    nodes = [
        {"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "o", "kind": "claim", "status": "conjectured", "owner": "me"},
    ]
    assert _has_error(_run(build_map(tmp_path, nodes, ["r"]), fast=True), 8)


def test_c8_all_reachable_ok(tmp_path):
    nodes = [
        {"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "c", "kind": "claim", "status": "conjectured", "owner": "me",
         "edges": [{"type": "discharges", "to": "r"}]},
    ]
    assert not _has_error(_run(build_map(tmp_path, nodes, ["r"]), fast=True), 8)


# --- Contract 9 -----------------------------------------------------------

def test_c9_adopted_route_no_needs_warns(tmp_path):
    nodes = [
        {"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "rt", "kind": "route", "status": "adopted", "owner": "me",
         "edges": [{"type": "discharges", "to": "r"}]},
    ]
    fs = _by_c(_run(build_map(tmp_path, nodes, ["r"]), fast=True), 9)
    assert any(f.level == "warning" for f in fs)


def test_c9_adopted_route_well_formed_ok(tmp_path):
    # route needs a stated claim AND carries a battery => gate (a)+(b) satisfied.
    nodes = [
        {"id": "g", "kind": "claim", "status": "stated", "lean": "G", "owner": "me"},
        {"id": "r", "kind": "claim", "status": "stated", "lean": "R", "owner": "me",
         "edges": [{"type": "discharges", "to": "g"}]},
        {"id": "rt", "kind": "route", "status": "adopted", "owner": "me",
         "kill": "battery/x.py",
         "edges": [{"type": "needs", "to": "r"}, {"type": "discharges", "to": "g"}]},
    ]
    findings = _run(build_map(tmp_path, nodes, ["g"]), fast=True)
    assert _by_c(findings, 9) == []
    assert not _has_error(findings, 1)  # acyclic


# --- Contract 10 ----------------------------------------------------------

def test_c10_selling_word_without_evidence_warns(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "conjectured", "owner": "me",
              "notes": "this is trivially true"}]
    fs = _by_c(_run(build_map(tmp_path, nodes, ["r"]), fast=True), 10)
    assert any("selling" in f.message for f in fs)


def test_c10_selling_word_with_evidence_ok(tmp_path):
    nodes = [{"id": "r", "kind": "claim", "status": "conjectured", "owner": "me",
              "notes": "this is trivially true", "kill": "battery/x.py"}]
    fs = _by_c(_run(build_map(tmp_path, nodes, ["r"]), fast=True), 10)
    assert not any("selling" in f.message for f in fs)
