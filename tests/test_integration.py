"""Integration: the genuine aoyagi-endgame fixture, survey fed from the real
cone_before_mint.json walker dump."""

import sys
import subprocess

from expedition_map import model, survey as sv, validate as V, views, battery, ops
from conftest import REPO, REAL_FIXTURE

LAUNCHER = REPO / "scripts" / "expedition"


def test_fixture_validates_with_no_errors(real_fixture_survey):
    m = model.load_map(real_fixture_survey)
    survey = sv.load_survey(m)
    findings = V.validate(m, survey, fast=False)
    errors, warnings = V.split(findings)
    assert errors == [], f"unexpected errors: {[repr(e) for e in errors]}"
    assert len(warnings) > 0  # cone-mode survey => several honest warnings


def test_fixture_expected_named_warnings(real_fixture_survey):
    m = model.load_map(real_fixture_survey)
    survey = sv.load_survey(m)
    findings = V.validate(m, survey, fast=False)
    msgs = [repr(f) for f in findings]
    # mint-108 anchor not in the proven root cone (it is the sorry-tainted goal).
    assert any("mint-108" in x and "not in root cone" in x for x in msgs)
    # box-threshold's dischargers are UNWITNESSED under a cone-mode survey.
    assert any("deeper-flag-shell-le" in x and "UNWITNESSED" in x for x in msgs)
    # the adopted direct route needs an only-adjudicated node (gate a).
    assert any(f.contract == 9 and f.node == "route-incidence-direct"
               for f in findings)


def test_fixture_box_threshold_anchor_in_cone(real_fixture_survey):
    # RouteMBoxThresholdFinite IS in the root cone => confirmed, no C2 warning.
    m = model.load_map(real_fixture_survey)
    survey = sv.load_survey(m)
    assert survey["nodes"]["box-threshold"]["in_cone"] is True
    findings = V.validate(m, survey, fast=False)
    assert not any(f.node == "box-threshold" and f.contract == 2 for f in findings)


def test_fixture_status_within_budget(real_fixture_survey):
    m = model.load_map(real_fixture_survey)
    survey = sv.load_survey(m)
    text = views.render_status(m, survey)
    assert len(text.splitlines()) <= 40


def test_fixture_brief_all_resolutions(real_fixture_survey):
    m = model.load_map(real_fixture_survey)
    survey = sv.load_survey(m)
    sizes = []
    for r in (1, 2, 3, 4):
        text, est = views.render_brief(m, survey, "deeper-flag-shell-le", r)
        assert text.strip()
        sizes.append(est)
    assert sizes == sorted(sizes) and len(set(sizes)) == 4


def test_fixture_battery_verdicts(real_fixture_survey):
    m = model.load_map(real_fixture_survey)
    results, _ = battery.run_battery(m)
    verdict = {r["script"]: r["verdict"] for r in results}
    assert verdict["w-333-bridge.py"] == "killed"
    assert verdict["w-666-u4.py"] == "killed"
    assert verdict["w-223-hpiv.py"] == "killed"
    assert verdict["w-selftest.py"] == "survives"
    assert verdict["w-corner-223.py"] == "survives"
    assert not any(v == "error" for v in verdict.values())


def test_fixture_anchors_emit(real_fixture_survey):
    m = model.load_map(real_fixture_survey)
    text, n = ops.anchors_emit(m)
    assert n >= 6  # the nodes with both lean + prop
    assert "#check @RouteMBoxThresholdFinite" in text


# --- CLI end-to-end via the launcher --------------------------------------

def _cli(map_dir, *args):
    return subprocess.run(
        [sys.executable, str(LAUNCHER), "--map", str(map_dir), *args],
        capture_output=True, text=True)


def test_cli_validate_fast_exit_zero():
    r = _cli(REAL_FIXTURE / "map", "validate", "--fast")
    assert r.returncode == 0, r.stderr
    assert "0 error" in r.stdout


def test_cli_view_tick_renders():
    # `view tick` prints the tick view without writing STATUS.md (no side effect
    # on the committed fixture; `status` is exercised via the model in-process).
    r = _cli(REAL_FIXTURE / "map", "view", "tick")
    assert r.returncode == 0, r.stderr
    assert "STATUS" in r.stdout


def test_cli_battery_run():
    r = _cli(REAL_FIXTURE / "map", "battery", "run")
    assert r.returncode == 0, r.stderr
    assert "KILLED" in r.stdout and "SURVIVES" in r.stdout
