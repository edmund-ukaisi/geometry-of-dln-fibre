# Threads — `determinantal-atlas`

Per-rung formaliser/reviewer threads (the ladder is in [`priorities.md`](priorities.md)). One **builder/committer**
per shared worktree at a time; read-only auditors run concurrently. Controller integrates + re-gates per
[`loop-prompt.md`](loop-prompt.md).

## P0 — recon

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P0 | scout | a687ac4d | ✅ DONE `787e688f` | verdict: mostly re-home/de-DLN-ify (overlap API + cover already built; residue bridge already proved); **capstone = BUILD** as a bespoke Zariski predicate over the rank-`r` open (NOT Mathlib `FiberBundle`, NOT over the closure). Refined ladder in `priorities.md`; report `threads/p0-recon/report.md` |

## Phase 1 — foundation (`det-atlas-p1`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P1.a | formaliser | abaaacd2 | ✅ DONE `f6684cf5` (re-home; full re-gate DEFERRED) | overlap API → `Core/RingTheory/Localization/Overlap.lean` (bare `Localization` ns); `Overlap.lean` + `FibreBundleTransition` green **standalone**, axiom-clean, consumers swept. Full-aggregator green pending (see below) |
| P1.b–e | — | — | ⏳ gated on box load | determinantal `(r+1)`-minor ideal (new) · rank strata + cover (re-home) · Schur coords (re-home) · dimension (Brick A cited) |

## ⚠ Build status — full re-gate DEFERRED (box load), NOT a correctness issue
- **Contamination (mine, fixed):** the worktree's `.lake` was warmed (`cp -al`) from the **pre-FL-III**
  `foundation-lift` worktree, leaving stale trdeg/Dimension oleans → spurious `Unknown constant Algebra.trdeg`
  at `Dimension/Localization`. Diagnosed as cache, not source (source correct, API present, dev sound, FL-III
  built it green). Fixed: `rm -rf .lake/build`. Clean rebuild built `Dimension/Integral` **green** with no
  `trdeg` error before being reaped. (→ lesson DA1.)
- **Deferral:** the box is saturated by parallel expeditions (aoyagi/main/genm builds), which OOM-reap a
  from-scratch det-atlas build. **Full-aggregator re-gate + P1.b dispatch are paused until box load subsides**
  (the idle heartbeat re-checks; verify no det-atlas lake is alive, then `scripts/lb` resumes from cache → green).
  (→ lesson DA2.)

## Phase 2 — constructive atlas + capstone (`det-atlas-p2`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P2.a–b | — | — | ⏳ | pivot-chart datum + fibre model · transitions |
| P2.c | — | — | ⏳ CRUX | cocycle compatibility — decorrelated review |
| P2.d | — | — | ⏳ CRUX (recon-gated) | bare `FiberBundle` capstone / residue-field-rank bridge — build iff detail-at-scale |

## Concurrency rule (this expedition)
At most **one builder/committer** in `.claude/worktrees/det-atlas` at a time (a second `lake build` corrupts
`.lake`; two `git commit`s race the index). Read-only auditors (no build, no commit) may run alongside one
builder. Rungs touching the same file are serialized.

_Updated each tick._
