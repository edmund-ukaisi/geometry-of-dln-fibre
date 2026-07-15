"""Battery: header parsing and exit-code -> verdict mapping."""

from expedition_map import model, battery
from conftest import build_map


def _battery_map(tmp_path):
    nodes = [
        {"id": "root", "kind": "claim", "status": "stated", "lean": "R", "owner": "me"},
        {"id": "dead", "kind": "route", "status": "refuted", "owner": "parked: x",
         "edges": [{"type": "forwarded-to", "to": "root"}]},
    ]
    md = build_map(tmp_path, nodes, ["root"])
    bdir = md / "battery"
    bdir.mkdir()
    (bdir / "w-kill.py").write_text(
        "# kills: dead\n# config: M=(3,3,3)\n# provenance: cert.md\n"
        "import sys\nprint('killed')\nsys.exit(1)\n")
    (bdir / "w-guard.py").write_text(
        "# guards: root\nimport sys\nprint('ok')\nsys.exit(0)\n")
    (bdir / "w-broken.py").write_text(
        "# kills: dead\nimport sys\nsys.exit(3)\n")
    (bdir / "_helper.py").write_text("X = 1\n")  # underscore: not run
    return md


def test_parse_header(tmp_path):
    md = _battery_map(tmp_path)
    hdr = battery.parse_header(md / "battery" / "w-kill.py")
    assert hdr["kills"] == ["dead"]
    assert hdr["config"] == "M=(3,3,3)"
    assert hdr["provenance"] == "cert.md"


def test_parse_header_multi_value(tmp_path):
    p = tmp_path / "s.py"
    p.write_text("# kills: a, b, c\nimport sys\nsys.exit(1)\n")
    assert battery.parse_header(p)["kills"] == ["a", "b", "c"]


def test_verdicts(tmp_path):
    md = _battery_map(tmp_path)
    m = model.load_map(md)
    results, skipped = battery.run_battery(m)
    by_name = {r["script"]: r for r in results}
    assert "_helper.py" not in by_name          # underscore skipped
    assert by_name["w-kill.py"]["verdict"] == "killed"
    assert by_name["w-guard.py"]["verdict"] == "survives"
    assert by_name["w-broken.py"]["verdict"] == "error"


def test_node_filter(tmp_path):
    md = _battery_map(tmp_path)
    m = model.load_map(md)
    results, skipped = battery.run_battery(m, node="root")
    names = {r["script"] for r in results}
    assert names == {"w-guard.py"}              # only the guard affects root
    assert skipped >= 1
