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
| P1.a | formaliser | abaaacd2 | ✅ DONE + RE-GATED `f6684cf5` | overlap API → `Core/RingTheory/Localization/Overlap.lean` (bare `Localization` ns); consumers swept. **Full-aggregator re-gate GREEN (3828 jobs), sorries 0, `awayTriple_cocycle` axiom-clean.** |
| P1.b | formaliser | a728b739 | ✅ DONE `d24f9b01` | `Core/RingTheory/Determinantal/Basic.lean` (bare `Matrix` ns): `detMinorPoly`/`eval_detMinorPoly` re-homed + generalized `Field→CommRing`; new `Matrix.determinantalIdeal` + API (`_mem_`, `_eq_span`, `_le_iff`). green 3829, sorries 0, axiom-clean |
| P1.c | formaliser | a4700497 | ✅ DONE `040a66e2` | `Strata.lean` (bare `Matrix`): rank strata + cover + connective `mem_rankLeLocus_iff_determinantalIdeal_le_ker` (field-level); `RankMinorCover` deleted, consumers swept. green 3829, sorries 0, axiom-clean, self-review+Codex PASS. (Tip advanced post-commit → L3 validated) |
| **P1.d** | formaliser | dispatching | 🔄 | Schur coords → `Core/RingTheory/Determinantal/Schur.lean`: `rank_fromBlocks_zero` (absent Mathlib), `rank_eq_iff_schur_eq`, `pivotRankChartEquiv`, `schurComplement_normal_form` (re-home `DeterminantalChart`/`SchurChartIff`/`SchurGauge`) |
| P1.e | — | — | ⏳ | dimension `r(n+m−r)` / codim `(n−r)(m−r)` (Brick A cited) |

## ✅ Build status — re-gate GREEN; contamination episode CLOSED
- **Contamination (mine, fixed + confirmed):** the worktree's `.lake` was warmed (`cp -al`) from the
  **pre-FL-III** `foundation-lift` worktree → stale trdeg/Dimension oleans → spurious `Unknown constant
  Algebra.trdeg`. Diagnosed as cache not source. Fixed: `rm -rf .lake/build` + clean rebuild → **full aggregator
  GREEN (3828 jobs), `Dimension/Localization.olean` BUILT**. dev sound throughout. (→ lesson DA1.)
- **Box-load episode (resolved):** under heavy parallel-expedition load the from-scratch build OOM-thrashed;
  deferred until the box quieted (18G free), then re-ran clean → green. The worktree now has a correct warm
  `.lake` for the remaining rungs (P1.b+ build incrementally). (→ lesson DA2.)

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
