"""Cordon → validate wiring (contract 12): blueprint-leak audit consumption."""

import json

from expedition_map import model, validate as V
from conftest import build_map


def _write_cordon(map_dir, cordon):
    sdir = map_dir / "survey"
    sdir.mkdir(exist_ok=True)
    (sdir / "cordon.json").write_text(json.dumps(cordon))


def _map(tmp_path):
    nodes = [
        {"id": "banked", "kind": "claim", "status": "proven", "lean": "Foo",
         "owner": "me"},
        {"id": "open", "kind": "claim", "status": "stated", "lean": "Bar", "owner": "me",
         "edges": [{"type": "discharges", "to": "banked"}]},
    ]
    return build_map(tmp_path, nodes, ["banked"])


def _c12(map_dir):
    m = model.load_map(map_dir)
    return [f for f in V.validate(m, None, fast=True) if f.contract == 12]


def test_no_cordon_no_findings(tmp_path):
    assert _c12(_map(tmp_path)) == []


def test_leak_on_banked_node_is_error(tmp_path):
    md = _map(tmp_path)
    _write_cordon(md, {"leaks": [{"decl": "DLN.Foo", "via": "blueprintX"}]})
    fs = _c12(md)
    errs = [f for f in fs if f.level == "error"]
    assert len(errs) == 1
    assert errs[0].node == "banked" and "blueprintX" in errs[0].message


def test_leak_not_matching_banked_is_warning(tmp_path):
    md = _map(tmp_path)
    # Bar belongs to `open` (stated, not banked) -> warning, not error.
    _write_cordon(md, {"leaks": [{"decl": "DLN.Bar", "via": "bp"}]})
    fs = _c12(md)
    assert not any(f.level == "error" for f in fs)
    assert any(f.level == "warning" and "Bar" in f.message for f in fs)


def test_unaccounted_is_warning(tmp_path):
    md = _map(tmp_path)
    _write_cordon(md, {"unaccounted": ["DLN.Something"]})
    fs = _c12(md)
    assert any(f.level == "warning" and "unaccounted" in f.message for f in fs)


def test_cited_not_flagged(tmp_path):
    md = _map(tmp_path)
    _write_cordon(md, {"cited": [{"axiom": "cited_aoyagi", "source": "Aoyagi"}]})
    assert _c12(md) == []


def test_cordon_error_fails_validate(tmp_path):
    md = _map(tmp_path)
    _write_cordon(md, {"leaks": [{"decl": "DLN.Foo", "via": "bp"}]})
    m = model.load_map(md)
    errors, _ = V.split(V.validate(m, None, fast=True))
    assert any(e.contract == 12 for e in errors)
