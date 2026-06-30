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
| **P2.c** | formaliser | acb882d6 | ✅ DONE + PUSHED `718e0583` | cocycle-compatibility (2-fold): `overlapTransition_trans_symm` (target-side round-trip `= AlgEquiv.refl`) + `overlapTransition_symm` (inverse characterization), in `AtlasTransition.lean`. **Pure groupoid algebra, no localization-element entry**: `self_trans_symm`/`symm_trans_self` FOUND in Mathlib v4.29 (not built), inner cancel → LANDED `chartOverlapTransitionK_trans_symm` → outer cancel. No whnf/kernel-cost trap (the recon's `@[reducible] targetChartLoc` worry did not bite). green 3832, sorries 0, axiom-clean `[propext, Classical.choice, Quot.sound]`. Executor's decorrelated Codex (xhigh): SOUND. **Controller fidelity pass: faithful, non-vacuous.** This IS the recon's "cocycle field" (lines 52/94/125) → **P2.d unblocked** |
| **P2.c′** | — | — | 🅿️ ROADMAPPED (NOT a P2.d blocker) | **triple cocycle** `g_{CE}=g_{DE}∘g_{CD}` on triple overlaps: genuinely ill-typed without a target-side `awayTriple` object (base side avoids via one-submonoid `awayTriple`; no target analogue). Needs a new sub-build — (i) target triple-localization, (ii) triple `awayCongr'`, (iii) restriction maps 2-fold→triple, (iv) naturality `restrict_overlapTransition_to_triple_eq_tripleTransition`, then cocycle by subsingleton (Codex-confirmed). Correctly NOT landed (the unanchored "cheaper partial" rejected — visible-progress, not bedrock). Belongs to the **R1 global-gluing** track, not the local-triviality predicate |
| **P2.d** | formaliser | p2d-capstone | ✅ DONE + PUSHED `7b43aaef` | **`Algebra.IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U`** (`LocalTriviality.lean`, bare `Algebra` ns): `ι` + `chart : ι → AtlasFibreChart` + `cover : (⋃ basicOpen chartElt) = U`. **Cocycle = derived lemma (not a field)** — `overlapTransition_trans_symm`/`_symm` from P2.c (holds for any `AtlasChart`s). DLN instance `reducedFibre_isZariskiLocallyTrivialAffineProduct` (`FibreZariskiLocalTriviality.lean`) at `U = rankROpen` (open, load-bearing — not `⊤`); new cover lemma `iUnion_pivotDatum_basicOpen_eq_rankROpen` (PivotDatum-indexed, le_antisymm via banked selector cover). green **3834**, sorries 0, **instance witness axiom-clean** = non-vacuity. Executor Codex (xhigh): clean on all 5 fidelity Qs. **Controller taste-check: faithful + sound.** |
| P2.d review | reviewer | p2d-review | ✅ DONE — **PASS-WITH-NITS** | decorrelated audit (`threads/p2d-review/verdict.md` + Codex): sound + faithful, no soundness/fidelity defect; new cover lemma correct (both inclusions), no global-bundle over-claim. **Independent re-gate GREEN 3834, sorries 0, axiom-clean** (= Phase-2 boundary re-gate). Two prose-precision nits FIXED `60fb928b`: Q2a (instance "non-vacuity/geometric witness/realized" → honest inhabited/satisfiable; `rankROpen ≠ ∅` not proved) + Q1c (cocycle decoupling line: on `trivK`/`M`, not the over-`BaseLoc` product). **Escalated to operator:** `Base → TotalRing/AmbientRing` rename (signature change — `Base` is the total/source ring by AG convention; docstrings flag it, mathematically fine) |

## Operator decisions (2026-06-30)
- **Capstone naming → BRIDGE, not keep-vs-rename.** Operator: build a bridge so the predicate retains its
  correct names in BOTH worlds (ring-theory `Base`/`BaseLoc` ↔ AG `total`/`base`/`fibre`/`projection`, via the
  `Spec`-contravariance flip) rather than pick one convention. → **rung P2.e** (additive view, keep `Base`/`BaseLoc`;
  scheme-side accessors PER-CHART; global fibration morphism R1-gated). Dispatched (`p2e-bridge`).
- **Phase-2 PR → AUTHORIZED** (operator authorized controller to open `det-atlas-p2 → dev`; merging stays
  operator's). Sequenced AFTER P2.e lands green, so the PR ships the complete both-worlds capstone in one piece.

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| **P2.e** | formaliser | p2e-bridge | 🔄 | two-worlds bridge view on `IsZariskiLocallyTrivialAffineProduct`: scheme-side accessors (`totalSpace = Spec Base`, `chartProjection i = comap structMap`, `fibreSpace`) + `Spec`-flip dictionary docstring; additive (keep `Base`/`BaseLoc`); per-chart projection only (global = R1-gated). Decorrelated Codex on the view shape |

## Phase 2 — boundary re-gate (controller) ✅ PASSED
Full aggregator GREEN (**3834 jobs**); sorries 0 / 0 axiom; the P2.d capstone (`reducedFibre_isZariskiLocallyTrivialAffineProduct`) + the abstract predicate's derived cocycle + the new cover lemma all axiom-clean `[propext, Classical.choice, Quot.sound]`; both DLN payoffs unchanged. Decorrelated review PASS-WITH-NITS, nits fixed (`60fb928b`). **Phase 2 COMPLETE (P2.a/b′/b/c/d) → ready for the Phase-2 PR (base `dev`, signal-and-wait).** Roadmapped-not-built: P2.c′ triple cocycle (R1 global-gluing track).

## Concurrency rule (this expedition)
At most **one builder/committer** in `.claude/worktrees/det-atlas` at a time (a second `lake build` corrupts
`.lake`; two `git commit`s race the index). Read-only auditors (no build, no commit) may run alongside one
builder. Rungs touching the same file are serialized.

_Updated each tick._
