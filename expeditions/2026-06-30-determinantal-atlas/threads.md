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
| P1.d | formaliser | a8eebf34 | ✅ DONE `e572b50f` | `Schur.lean` (bare `Matrix`): `rank_fromBlocks_zero`, `pivotRankChartEquiv` (`finrank=r(p+q−r)`), `rank_eq_iff_schur_eq`, `schurComplement_normal_form`; `DeterminantalChart`+`SchurChartIff` deleted, `SchurGauge` kept (DLN gauge). green 3828, sorries 0, axiom-clean |
| P1.e | formaliser | a6a886c2 | ✅ DONE `f2cd20af` | `Dimension.lean` (bare `Matrix`, engine-free): `rankStratumDim`/`Codim` + `codim+dim=ambient` + finrank-anchor to the pivot chart; engine-bound `varietyDim_…_stratum`/`height_…` re-pointed + "Proved, not cited" docstrings. green 3829, sorries 0, axiom-clean. **PRECISION CORRECTION: Brick A is Proved (zero-cited, via the orbit codim engine), NOT cited — reviewer+Codex confirmed; my brief's "cited" tag was wrong** |

## Phase 1 — boundary re-gate (controller) ✅ PASSED
Full build green (3829 jobs); sorries 0 / **0 axiom**; axioms `[propext, Classical.choice, Quot.sound]` on all
Phase-1 headlines (`rankStratumCodim_add_rankStratumDim_eq` even pure `Nat`), on the engine-bound
`varietyDim_productRankLocusLE_stratum` (**Brick A Proved — no global axiom**), and on **both DLN payoffs
(unchanged)**. **Phase 1 complete → PR opened (base `dev`); proceeding to Phase 2.**

## ✅ Build status — re-gate GREEN; contamination episode CLOSED
- **Contamination (mine, fixed + confirmed):** the worktree's `.lake` was warmed (`cp -al`) from the
  **pre-FL-III** `foundation-lift` worktree → stale trdeg/Dimension oleans → spurious `Unknown constant
  Algebra.trdeg`. Diagnosed as cache not source. Fixed: `rm -rf .lake/build` + clean rebuild → **full aggregator
  GREEN (3828 jobs), `Dimension/Localization.olean` BUILT**. dev sound throughout. (→ lesson DA1.)
- **Box-load episode (resolved):** under heavy parallel-expedition load the from-scratch build OOM-thrashed;
  deferred until the box quieted (18G free), then re-ran clean → green. The worktree now has a correct warm
  `.lake` for the remaining rungs (P1.b+ build incrementally). (→ lesson DA2.)

## Phase 2 — constructive atlas + capstone (`det-atlas-p2`, off `-p1`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P2.a | formaliser | a9f9042b | ✅ DONE `5aad04f5` | `Atlas.lean` (bare `Algebra` ns): `StandardFibreChart` (structMap/triv/flat) + `flatModel`/`ofTrivialization`; DLN `standardFibreChartOfPivot` the non-vacuous instance. green 3830, axiom-clean; aggregator-wired at integration |
| P2.b′ | formaliser | a50b98e3 | ✅ DONE `50a6842d` | `AlgEquiv` groupoid laws (`trans_assoc`/`trans_refl`/`refl_trans`, `ext;rfl`) → `Core/Algebra/AlgEquiv/Groupoid.lean`; sibling-clash confirmed absent; axioms just `[Quot.sound]`. green 3831 |

> **#20 review fixes merged forward** (`58c661b7`): PR #20's three points (Schur `prodLequiv`→`private`; `rankStratumDim` docstring scoped to `r ≤ min p q`; priorities/Dimension prose Brick-A→Proved) landed on `det-atlas-p1` (`5d846875`, threads replied + resolved) and merged into `det-atlas-p2`; re-gate green 3830.
| **P2.b** | formaliser | acb882d6 | ✅ DONE + PUSHED `541bf5d3` | `Core/RingTheory/Determinantal/AtlasTransition.lean` (bare `Algebra` ns): `AtlasChart` (chartElt + bare-`k` `trivK` — Flag 2 pairing) + `overlapElt`/`targetChartLoc`/`overlapTriv`/`chartOverlapTransitionK`(+`_apply`/`_trans_symm`)/`overlapTransition`; `AtlasFibreChart extends AtlasChart` carries `StandardFibreChart`. `awayCongr'`(+`_symm`) re-homed to `Localization/Overlap.lean`. DLN `FibreTargetOverlap` re-homed: `pivotAtlasChart` the instance, base-side transition + round-trip = abstract `Algebra.AtlasChart.…` at the pivot charts; target-side kept one-`Away`-layer (instance-synth). Codex (xhigh) design-vetted Option C. **Flag 3 dodged** (bare-`k` trivK, no over-base `triv` in transition path — no diamond). full green 3832, sorries 0, axiom-clean `[propext, Classical.choice, Quot.sound]`. Cocycle set up reachable via groupoid laws (P2.c) |
| **P2.c** | formaliser | (dispatched) | 🔄 CRUX | cocycle-compatibility: target-side round-trip `overlapTransition C D ≪≫ overlapTransition D C = refl` (+ `.symm` characterization), purely via groupoid laws + LANDED `chartOverlapTransitionK_trans_symm` (no localization-element entry). Triple cocycle: assess+attempt (base-side `awayTriple_cocycle` proved P1.a); if heavy transport needed → report + scope. Decorrelated review |
| P2.d | — | — | ⏳ CRUX (BUILD) | **bespoke `IsZariskiLocallyTrivialAffineProduct` over the rank-`r` open** (NOT Mathlib `FiberBundle`); cover-every-scheme-point via the already-proved `FibreRankBridge` — decorrelated review |

## Concurrency rule (this expedition)
At most **one builder/committer** in `.claude/worktrees/det-atlas` at a time (a second `lake build` corrupts
`.lake`; two `git commit`s race the index). Read-only auditors (no build, no commit) may run alongside one
builder. Rungs touching the same file are serialized.

_Updated each tick._
