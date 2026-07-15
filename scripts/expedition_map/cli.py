"""CLI dispatch. Every command resolves a map and runs the validator; contract
errors exit nonzero, warnings do not (unless ``--strict``)."""

from __future__ import annotations

import sys
import json
import argparse
from pathlib import Path

from . import model, survey as survey_mod, validate as validate_mod
from . import views, battery as battery_mod, ops


def _load(args):
    map_dir = model.resolve_map_dir(getattr(args, "map", None))
    return model.load_map(map_dir)


def _print_findings(findings, stream=sys.stderr):
    errors, warnings = validate_mod.split(findings)
    for f in errors:
        print("  " + repr(f), file=stream)
    for f in warnings:
        print("  " + repr(f), file=stream)
    return errors, warnings


def _guard(m, args, fast=True):
    """Run the validator as a gate. Returns exit code (0 = proceed)."""
    survey = survey_mod.load_survey(m)
    findings = validate_mod.validate(m, survey, fast=fast)
    errors, warnings = validate_mod.split(findings)
    if errors:
        print(f"validator: {len(errors)} error(s) block this command:", file=sys.stderr)
        _print_findings(errors)
        return 2
    if warnings and getattr(args, "strict", False):
        print(f"validator (--strict): {len(warnings)} warning(s):", file=sys.stderr)
        _print_findings(warnings)
        return 2
    if warnings:
        print(f"(validator: {len(warnings)} warning(s); use `validate` to see)",
              file=sys.stderr)
    return 0


# ---------------------------------------------------------------------------
# commands
# ---------------------------------------------------------------------------

def cmd_validate(args):
    m = _load(args)
    survey = survey_mod.load_survey(m)
    if survey is None and not args.fast:
        print("note: no survey present — survey-dependent checks (3/4/5) skipped; "
              "run `expedition survey` for a full check.", file=sys.stderr)
    findings = validate_mod.validate(m, survey, fast=args.fast)
    errors, warnings = _print_findings(findings, stream=sys.stdout)
    mode = "fast" if args.fast else "full"
    print(f"\nvalidate ({mode}): {len(errors)} error(s), {len(warnings)} warning(s)")
    if errors:
        return 1
    if warnings and args.strict:
        return 1
    return 0


def cmd_survey(args):
    m = _load(args)
    src = args.source
    if not src:
        default = Path(m["map_dir"]) / "survey" / "walker.json"
        if default.is_file():
            src = str(default)
        else:
            print("survey: need --from <walker.json> (no survey/walker.json found)",
                  file=sys.stderr)
            return 2
    with open(src) as fh:
        data = json.load(fh)
    survey = survey_mod.build_survey(m, data, src)
    path = survey_mod.write_survey(m, survey)
    fh_ = survey["freshness"]
    print(f"survey written: {path}")
    print(f"  mode={fh_['walker_mode']}  decls={fh_['n_decls']}  "
          f"head={(fh_['git_head'] or 'no-git')[:8]}")
    print(f"  orphans={len(survey['orphans'])}  "
          f"live-sorry={len(survey['live_sorry'])}  "
          f"witness-edges={len(survey['witness'])}")
    return 0


def cmd_status(args):
    m = _load(args)
    rc = _guard(m, args)
    if rc:
        return rc
    survey = survey_mod.load_survey(m)
    path, text = views.write_status(m, survey)
    print(text, end="")
    print(f"\n(written to {path})", file=sys.stderr)
    return 0


def cmd_view(args):
    m = _load(args)
    rc = _guard(m, args)
    if rc:
        return rc
    survey = survey_mod.load_survey(m)
    which = args.which
    if which == "tick":
        print(views.render_status(m, survey), end="")
    elif which == "decision":
        if not args.id:
            print("view decision: need an <id>", file=sys.stderr)
            return 2
        print(views.render_decision(m, survey, args.id), end="")
    elif which == "lookahead":
        print(views.render_lookahead(m, survey), end="")
    elif which == "dag":
        print(views.render_dag(m, kind=args.kind, status=args.status,
                               landmarks_only=args.landmarks), end="")
    else:
        print(f"unknown view {which!r}", file=sys.stderr)
        return 2
    return 0


def cmd_brief(args):
    m = _load(args)
    rc = _guard(m, args)
    if rc:
        return rc
    survey = survey_mod.load_survey(m)
    text, _ = views.render_brief(m, survey, args.id, args.resolution)
    print(text, end="")
    return 0


def cmd_battery(args):
    m = _load(args)
    results, skipped = battery_mod.run_battery(
        m, node=args.node, run_all=args.all)
    if not results:
        print(f"battery: no scripts matched (skipped {skipped})")
        return 0
    print(f"# battery run  ({len(results)} script(s), {skipped} skipped)\n")
    n_err = 0
    for r in results:
        rel = "kills " + ",".join(r["kills"]) if r["kills"] else ""
        rel += (("  guards " + ",".join(r["guards"])) if r["guards"] else "")
        print(f"  {r['verdict'].upper():9s} {r['script']:22s} exit={r['exit']}  {rel}")
        if r["config"]:
            print(f"            config: {r['config']}")
        if r["verdict"] == "error":
            n_err += 1
            for ln in r["output_tail"]:
                print(f"            ! {ln}")
    print(f"\naffected nodes: " + ", ".join(sorted(
        {n for r in results for n in (r['kills'] + r['guards'])})))
    return 1 if n_err else 0


def cmd_rename(args):
    m = _load(args)
    msg = ops.rename(m["map_dir"], args.old, args.new)
    print(msg)
    return 0


def cmd_tombstone(args):
    m = _load(args)
    msg = ops.tombstone(m["map_dir"], args.id, args.forward, args.reason)
    print(msg)
    return 0


def cmd_new(args):
    print(ops.scaffold(args.kind, args.id), end="")
    return 0


def cmd_calibration(args):
    m = _load(args)
    if args.action == "add":
        print(ops.calibration_add(m["map_dir"], args.node, args.predicted, args.actual))
    else:
        print(ops.calibration_show(m["map_dir"]))
    return 0


def cmd_anchors(args):
    m = _load(args)
    text, npinned = ops.anchors_emit(m, out=args.out)
    if args.out:
        print(f"anchors emitted: {args.out}  ({npinned} pin(s))")
    else:
        print(text, end="")
    return 0


# ---------------------------------------------------------------------------
# argparse
# ---------------------------------------------------------------------------

def build_parser():
    p = argparse.ArgumentParser(prog="expedition", description=__doc__)
    p.add_argument("--map", help="map directory (default: ./map or expeditions/*/map)")
    p.add_argument("--strict", action="store_true", help="treat warnings as errors")
    sub = p.add_subparsers(dest="cmd", required=True)

    sp = sub.add_parser("validate", help="run contracts 1-10")
    sp.add_argument("--fast", action="store_true", help="structural only (skip 3/4/5)")
    sp.set_defaults(func=cmd_validate)

    sp = sub.add_parser("survey", help="build survey/*.json from a walker dump")
    sp.add_argument("--from", dest="source", help="walker JSON dump")
    sp.set_defaults(func=cmd_survey)

    sp = sub.add_parser("status", help="materialize STATUS.md (tick view)")
    sp.set_defaults(func=cmd_status)

    sp = sub.add_parser("view", help="render a view")
    sp.add_argument("which", choices=["tick", "decision", "lookahead", "dag"])
    sp.add_argument("id", nargs="?", help="node id (for decision)")
    sp.add_argument("--kind", choices=list(model.KINDS), help="dag filter")
    sp.add_argument("--status", help="dag filter")
    sp.add_argument("--landmarks", action="store_true",
                    help="dag: only landmark nodes + edges among them")
    sp.set_defaults(func=cmd_view)

    sp = sub.add_parser("brief", help="teammate context bundle")
    sp.add_argument("id")
    sp.add_argument("--resolution", type=int, default=2, choices=[1, 2, 3, 4])
    sp.set_defaults(func=cmd_brief)

    sp = sub.add_parser("battery", help="run battery scripts")
    sp.add_argument("action", choices=["run"])
    sp.add_argument("--node", help="only scripts affecting this node")
    sp.add_argument("--all", action="store_true", help="run all (default anyway)")
    sp.set_defaults(func=cmd_battery)

    sp = sub.add_parser("rename", help="atomic id rename + forwarding pointer")
    sp.add_argument("old")
    sp.add_argument("new")
    sp.set_defaults(func=cmd_rename)

    sp = sub.add_parser("tombstone", help="retire a node with a forwarding edge")
    sp.add_argument("id")
    sp.add_argument("--forward", required=True, help="target node id")
    sp.add_argument("--reason", required=True, help="one-line reason")
    sp.set_defaults(func=cmd_tombstone)

    sp = sub.add_parser("new", help="scaffold a node block (printed, not inserted)")
    sp.add_argument("kind", choices=list(model.KINDS))
    sp.add_argument("id")
    sp.set_defaults(func=cmd_new)

    sp = sub.add_parser("calibration", help="prediction-vs-actual ledger")
    sp.add_argument("action", choices=["add", "show"])
    sp.add_argument("--node")
    sp.add_argument("--predicted")
    sp.add_argument("--actual")
    sp.set_defaults(func=cmd_calibration)

    sp = sub.add_parser("anchors", help="emit MapAnchors.lean (#check pins)")
    sp.add_argument("action", choices=["emit"])
    sp.add_argument("--out", help="write to this file instead of stdout")
    sp.set_defaults(func=cmd_anchors)

    return p


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except model.MapError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
