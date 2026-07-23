#!/usr/bin/env python3
"""Generate the dependency-landscape site for a branch.

Typical invocation (from this directory):

    python3 generate.py --profile profiles/aoyagi-engine.json \
        --repo ../.. --rev origin/expedition/aoyagi-engine \
        --out out/aoyagi-engine

Reads git only (no checkout, no Lean build). The base of the history playback
defaults to the merge-base with origin/dev.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import shutil
import sys
from pathlib import Path

TOOL = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOL))

from landscape.config import Profile
from landscape.gitio import Repo
from landscape.history import BlobCache, build_history
from landscape import current, planmap


def emit_js(path: Path, var: str, payload: dict):
    path.write_text(f"window.{var}=" + json.dumps(payload, separators=(",", ":")) + ";")
    print(f"[emit] {path.name} ({path.stat().st_size // 1024} KB)")


def write_readme(out: Path, hist_meta, decl_meta, mod_meta, args):
    audit = hist_meta["timingAudit"]
    out.joinpath("README.md").write_text(f"""# Lean dependency landscape — {hist_meta['branch']}

Generated {hist_meta['generatedAt']} by `tools/dependency-landscape/generate.py`
against `{hist_meta['branch']}` at `{hist_meta['head'][:10]}` (read-only: no checkout, no Lean build).

## Views

- `index.html` — {mod_meta['nodeCount']} modules, {mod_meta['edgeCount']} direct project imports.
- `declarations.html` — {decl_meta['nodeCount']} source declarations, {decl_meta['edgeCount']} name-resolved project references.
- `density.html` — layer-density profile (scope / kind / area / scale controls).
- `landscape.html` — multiscale quotient DAG with weighted dependency ribbons.
- `history.html` — hourly playback: {hist_meta['timelineFrameCount']} frames,
  {hist_meta['uniqueStateCount']} distinct code states, goal-cone scope, proof-role lanes,
  proof debt, churn, hubs, structural deltas{", plan-layer panel" if hist_meta.get('planAvailable') else ""}.
- `map.html` — the expedition plan map (claims.yaml mined over its git history):
  structure DAG + status lifelines, battery attachments, plan⇄territory join.

## Method, honestly

- **Source-resolved, not elaborated.** Declarations are the explicitly authored
  commands found in the Lean source; references are name-resolved from tokens
  (namespace/open-aware, suffix fallback). Proof roles and code areas are
  name-derived heuristics from `profiles/{args.profile_name}`. No `.olean` was read;
  treat edges and roles as approximate.
- **Vertical coordinate** = dependency height, 0 at top-level consumers/unused
  roots, growing downward toward shared foundations. Same-height cycles (mutual
  or resolution-induced) are SCC-condensed so every displayed ribbon points
  strictly upward from prerequisite to consumer.
- **Playback clock** = first-parent committer time on
  `{hist_meta['base'][:10]}..{hist_meta['head'][:10]}`: a side branch enters
  atomically at its merge. Timing audit: {audit['firstParentCommitCount']} first-parent commits,
  {audit['mergeCommitCount']} merges, {audit['sideBranchCommitCount']} side-branch commits,
  {audit['authorCommitterMismatchCount']} author/committer differences
  (max {audit['maxAbsAuthorCommitterDeltaSeconds']}s), {audit['committerTimestampBackstepCount']} backsteps.
- **Goal cone** follows the first available headline among
  {', '.join('`' + c + '`' for c in hist_meta['goalCandidates'])} in each snapshot.
- **Frontier** = declarations whose source contains `sorry`, plus (as a cone)
  everything they depend on.

Regenerate: `python3 tools/dependency-landscape/generate.py --profile
tools/dependency-landscape/profiles/{args.profile_name} --rev {args.rev} --out <dir>`.
""")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--profile", required=True)
    ap.add_argument("--repo", default=str(TOOL.parent.parent))
    ap.add_argument("--rev", required=True, help="branch / rev to visualise")
    ap.add_argument("--base", default=None,
                    help="history base rev (default: merge-base with origin/dev)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--bucket-hours", type=int, default=None)
    ap.add_argument("--map-path", default=None,
                    help="expedition map claims.yaml (default: newest at tip)")
    ap.add_argument("--no-history", action="store_true")
    ap.add_argument("--max-states", type=int, default=None,
                    help="smoke-test cap on distinct history states")
    args = ap.parse_args()

    profile = Profile.load(args.profile)
    args.profile_name = Path(args.profile).name
    if args.bucket_hours:
        profile.bucket_hours = args.bucket_hours
    repo = Repo(args.repo)
    head = repo.rev_parse(args.rev)
    base = repo.rev_parse(args.base) if args.base else repo.merge_base("origin/dev", head)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    blobs = BlobCache(repo)

    print(f"[tip] {args.rev} = {head[:10]}; scanning tip state…")
    tip = current.tip_state(repo, head, profile, blobs)
    print(f"[tip] {tip[0].n} declarations, {tip[0].edge_count} refs, "
          f"max height {tip[0].max_height}, goal = {tip[0].goal_target}")

    map_path = args.map_path or planmap.find_map_path(repo, head)
    plan = planmap.mine(repo, base, head, map_path, tip[0]) if map_path else None
    if plan:
        plan["meta"]["branch"] = args.rev
        plan["meta"]["head"] = head[:10]
        emit_js(out / "map-data.js", "MAP_DATA", plan)
        print(f"[plan] {map_path}: {plan['meta']['liveCount']} live nodes "
              f"(+{plan['meta']['archivedCount']} archived), "
              f"{plan['meta']['commitCount']} map commits, "
              f"{len(plan['epochs'])} re-root(s)")
    else:
        emit_js(out / "map-data.js", "MAP_DATA", {"meta": {"mapPath": None}, "nodes": [],
                                                  "events": [], "epochs": [], "battery": []})
        print("[plan] no expeditions/*/map/claims.yaml at tip — plan layer empty")

    mod = current.build_module_graph(repo, args.rev, head, profile, blobs, tip)
    emit_js(out / "module-data.js", "GRAPH_DATA", mod)
    dec = current.build_declaration_graph(repo, args.rev, head, profile, blobs, tip, plan)
    emit_js(out / "declaration-data.js", "GRAPH_DATA", dec)

    hist = None
    if not args.no_history:
        hist = build_history(repo, base, head, profile,
                             progress=lambda s: print(f"\r[history] {s}", end="", flush=True),
                             max_states=args.max_states,
                             plan_clock=planmap.PlanClock(plan) if plan else None)
        print()
        hist["meta"]["branch"] = args.rev
        hist["meta"]["planAvailable"] = bool(plan)
        emit_js(out / "history-data.js", "HISTORY_DATA", hist)

    for asset in (TOOL / "viewers").iterdir():
        shutil.copy(asset, out / asset.name)
    if hist:
        write_readme(out, hist["meta"], dec["meta"], mod["meta"], args)
    print(f"[done] open {out}/index.html")
    repo.close()


if __name__ == "__main__":
    main()
