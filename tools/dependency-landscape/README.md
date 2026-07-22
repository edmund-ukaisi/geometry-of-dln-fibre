# dependency-landscape — the expedition comprehension instrument

Generates a self-contained HTML visualisation suite over a Lean expedition
branch: the module import forest, the source-resolved declaration DAG, a
layer-density profile, a multiscale quotient landscape, and — the centrepiece —
an **hourly Git-history playback** of the declaration DAG along the branch's
first-parent integration spine (goal-cone scope, proof-role lanes, proof debt,
churn, dependency hubs, structural deltas).

This is the committed, configurable rebuild of the ad-hoc `/tmp` tool that
produced the 2026-07-15 `geometry-of-dln-fibre-dependency-graphs` output (and
the Quillen–Suslin landscape); the viewer UI is inherited from that output and
adapted to be profile-driven rather than hardcoded.

## Run

```bash
cd tools/dependency-landscape
python3 generate.py --profile profiles/aoyagi-engine.json \
    --rev origin/expedition/aoyagi-engine \
    --out out/aoyagi-engine
# then open out/aoyagi-engine/index.html in a browser
```

- `--repo` defaults to the repository containing this tool; any clone/worktree
  works — all reads go through the shared git object store.
- `--base` defaults to `merge-base(origin/dev, rev)`; the playback covers
  `base..rev` on the first-parent lineage.
- `--bucket-hours`, `--max-states` (smoke tests), `--no-history` are available.
- Pure Python 3 + git; **no checkout, no Lean build, no network**. Output goes
  under `out/` (gitignored).

## What it computes, honestly

- **Source-resolved, not elaborated.** Declarations are the explicitly authored
  commands found in the Lean source at each historical state (read from git
  blobs); references are name-resolved from identifier tokens — namespace- and
  `open`-aware exact lookup, plus a suffix fallback that only fires for
  partially-qualified uppercase-headed tokens (bare identifiers and hypothesis
  dot-notation like `h.symm` never suffix-match; that class was measured to
  fabricate ~1,300-consumer phantom hubs). Treat edges as approximate; the UI
  labels them as such.
- **Heights**: 0 = top-level consumers / unused roots, growing downward to
  shared foundations. Same-height cycles (mutual or resolution-induced) are
  SCC-condensed so every displayed ribbon points strictly upward from
  prerequisite to consumer.
- **Playback clock** = first-parent committer time: a side branch enters
  atomically at its merge, never as a fictitious linear worktree. A timing
  audit (merges, author/committer skews, backsteps) is embedded in the output
  and shown in the legend.
- **Goal cone** = transitive dependencies of the first available headline among
  the profile's `goalCandidates`, re-resolved per snapshot.
- **Frontier** = declarations whose source contains `sorry`, and (as a cone)
  everything they depend on. This differs from the 07-15 ad-hoc run, whose
  frontier came from hand-authored planning overlays.
- **Proof roles / code areas / milestone tags** are regex heuristics from the
  profile, not elaborator facts.

## Profiles

`profiles/<name>.json` carries everything expedition-specific: lean root,
area rules (module-name regexes, first match wins), proof-role rules
(name+module regexes), display orders and colors, goal candidates, milestone
tag rules. The viewers read all labels/colors/orders from the emitted
metadata — nothing expedition-specific is hardcoded in JS. To visualise
another expedition (or another repo), write a profile and point `--repo`/
`--rev` at it.

## Layout of this directory

- `generate.py` — CLI entry; emits `module-data.js`, `declaration-data.js`,
  `history-data.js`, copies `viewers/`, writes the output `README.md`.
- `landscape/` — the package: `gitio` (plumbing incl. batched blob reads),
  `leanparse` (heuristic Lean scanner), `graph` (resolution, SCC, heights,
  cones, quotient), `history` (lineage, hourly frames, states, audit),
  `current` (tip graphs + layered barycenter layout), `config` (profiles).
- `viewers/` — static HTML/CSS/JS, adapted from the 07-15 reference output.
- `out/` — generated sites (gitignored; regenerate at will).

## Performance notes

Blob parses are cached by blob sha; graph computation is cached by the lean
tree object id, so docs-only commits are free. A full ~600-state history over
a ~10k-declaration codebase takes on the order of an hour; use
`--max-states 5` for smoke tests and `--bucket-hours 4` for a quick coarse
playback.
