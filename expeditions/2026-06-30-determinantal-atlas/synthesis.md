# Synthesis — `determinantal-atlas`

_Accumulates as rungs land. Final synthesis at close._

## Kickoff (2026-06-30)
Fourth **build-the-buildable** expedition, on `origin/dev` `a13b11f2` (after #14 dimension stack + FL-II + FL-III
orbit squeeze). Central question: build a Mathlib-grade, network-free `Core` library for **determinantal rank
geometry + the constructive pivot-chart atlas** (localization-overlap API → determinantal rank-stratum API →
per-pivot Schur trivializations + cocycle compatibility + a recon-gated bare `FiberBundle` capstone), and
re-express the DLN rank-locus wrappers as instances. Source: `/tmp/next_foundational_expedition_recommendation.md`
(Primary programme).

**Why (operator-confirmed):** consolidates the existing-but-scattered chart machinery (`dStratum`,
`productRankLocusLE`, `sigmaIdeal`, `RepCoord`, fragile double-localizations) into its honest, named,
**constructive**, reusable form — standard determinantal AG, the team's detail-at-scale strength. Core engine +
thin DLN adapter (the FL-III pattern). Foundation-cleanliness/bedrock, not a stuck headline.

**The constructive virtue:** the atlas is explicit + finite + computable — pivots indexed by (`r`-row, `r`-col)
subsets, charts `U_P = D(det A_P)`, trivializations the closed-form Schur `D = C A⁻¹ B`, transitions explicit
rational maps. Prefer constructive over abstract-existence throughout.

**The one discrimination (recon-gated):** the bare-`FiberBundle` capstone needs a **residue-field-rank bridge**
(charts cover every *scheme point*, not just `k`-rational ones). Likely detail-at-scale (basic-opens-cover +
minor↔rank over `κ(p)`), not a monument — recon confirms; build if so, else atlas+cocycle is the honest ceiling
+ roadmap the leap. The constructive atlas does not depend on the bare-bundle repackaging.

## Roadmap addition (this expedition)
The **RLCT generic-foundation programme** is written into [`ROADMAP.md`](../../ROADMAP.md) — the integrability-
threshold / zeta-pole RLCT definition, the generic invariance theorems, the normal-crossing certificate layer,
the quarantined citations, and the honest DLN payoff boundary. Tracked as the important next-after-this
programme; NOT built here (operator's scope call — clean scope over premature analysis).

## P0 — recon ✅ (`787e688f`; report `threads/p0-recon/report.md`)
**Two headline findings (scout + decorrelated Codex xhigh):**

1. **The expedition is overwhelmingly re-home + de-DLN-ify, not fresh build.** The overlap API (P1.a) — incl.
   the **triple-overlap cocycle, proved** — already exists DLN-free over arbitrary `CommRing`
   (`FibreBundleTransition` §Abstract/§Triple); the minor↔rank cover (P1.b/c) is general field-level
   (`Matrix/RankMinors`, `RankMinorCover`); and the gating P2.d crux, the **residue-field-rank bridge, is
   already proved** for the DLN instance (`FibreRankBridge.mem_rankROpen_iff_rank_universalMatrixResidue_eq`).
   So most rungs are L7 re-homes/generalizes; the genuinely-new defs are the determinantal `(r+1)`-minor ideal
   (P1.b) and the small `AlgEquiv`-groupoid spin-out (P2.b′). Lower risk than anticipated — FL-III-Phase-1-shaped.

2. **Capstone = BUILD, with a framing correction (adopted).** The "bare Mathlib `FiberBundle`" target was wrong:
   Mathlib's `FiberBundle` is **topological only** (no scheme/Zariski class at this pin), and a bundle over the
   **closure** `Σ̄^r` is genuinely **false** (the rank-`<r` boundary lies in no chart). The honest capstone is a
   **bespoke `IsZariskiLocallyTrivialAffineProduct` over the rank-`r` open** — `FibreBundleHeadline` already
   packages it except the cocycle field. The only blocker (`AlgEquiv.trans_assoc`/`refl`, absent in v4.29)
   dissolves by `ext x; rfl` (scratch-compiled clean) → rung P2.b′. **No monument on the path, no fallback
   expected.** (This resolves the earlier `locallyTrivial` reservation: the bridge is proved + detail-at-scale;
   the right target is the bespoke predicate over the open, not Mathlib's topological bundle.)

The refined rung ladder + the de-DLN-ify target list are in [`priorities.md`](priorities.md) (from the report's §4).

## Phase 1 / Phase 2
**P1.a (overlap-API re-home) landed clean** (`f6684cf5`): `Core/RingTheory/Localization/Overlap.lean`, bare
`Localization` namespace (L7), `Overlap.lean` + `FibreBundleTransition` green standalone, axiom-clean, consumers
swept. The re-home WORK is correct + done.

**Build episode (banked, lessons DA1/DA2):** the full aggregator hit a spurious `Unknown constant Algebra.trdeg`
at `Dimension/Localization` — **my own cache contamination**, not a regression: I warmed the worktree's `.lake`
from the pre-FL-III `foundation-lift` (FL-III restructured the trdeg/Dimension stack). Diagnosed cleanly (source
correct, `Algebra.trdeg` present, FL-III green on dev), fixed by nuking `.lake/build`; the clean rebuild built
`Dimension/Integral` green with no error before being **reaped under heavy multi-expedition box load**.
**RESOLVED:** when the box quieted (18G free), the clean rebuild ran to a **full-aggregator GREEN (3828 jobs)** with
`Dimension/Localization.olean` BUILT — contamination confirmed-fixed, dev sound, P1.a re-gate passed (sorries 0,
`awayTriple_cocycle` axiom-clean). The worktree now has a correct warm `.lake`; P1.b+ build incrementally.
**Phase 1 resumed: P1.b dispatched** (matrix coord ring + the determinantal `(r+1)`-minor ideal).

## Phase 1 CLOSE (2026-06-30)
All five rungs landed; controller boundary re-gate PASSED (full build 3829 jobs green, sorries 0 / 0 axiom,
axioms `[propext, Classical.choice, Quot.sound]` on every headline + both DLN payoffs unchanged). The
determinantal/atlas foundation is Mathlib-grade, **bare `Matrix`/`Localization` namespaces** (L7, file-move-ready),
DLN instances preserved:
- `Core/RingTheory/Localization/Overlap.lean` — overlap API + triple cocycle (P1.a).
- `Core/RingTheory/Determinantal/Basic.lean` — `detMinorPoly` + the determinantal `(r+1)`-minor ideal (P1.b).
- `Core/RingTheory/Determinantal/Strata.lean` — rank strata + pivot cover + the ideal↔rank-locus connective (P1.c).
- `Core/RingTheory/Determinantal/Schur.lean` — block-rank additivity + `pivotRankChartEquiv` + rank↔Schur iff (P1.d).
- `Core/RingTheory/Determinantal/Dimension.lean` — `rankStratumDim/Codim` closed forms + `codim+dim=ambient` (P1.e).
- Deleted (emptied): `RankMinorCover`, `DeterminantalChart`, `SchurChartIff`.

**Precision correction (P1.e, banked):** the recon's "rides cited Brick A" was a mis-tag I propagated into the P1.e
brief. Brick A (`codim Σ̄^r = C`) is **Proved zero-cited** in-repo (re-derived from the quiver-orbit codim engine —
no Eagon–Northcott/Bruns–Vetter citation, `#print axioms` standard-3). So the dimension headlines are honestly
**Proved**; a `_of_brickA`/cited framing would have been the *inverse* overclaim (under-claiming a Proved result).
Reviewer + decorrelated Codex (xhigh) confirmed. name=content cuts both ways.

## Phase 2 CLOSE (2026-06-30)
All five rungs landed; controller boundary re-gate + decorrelated review PASSED. The constructive pivot-chart
atlas and its capstone are built — network-free `Core`, bare `Algebra`/`AlgEquiv` namespaces (L7), DLN as the
instance. New `Core` API (all axiom-clean `[propext, Classical.choice, Quot.sound]`):
- `Core/RingTheory/Determinantal/Atlas.lean` — `Algebra.StandardFibreChart` (P2.a): the per-chart fibre model
  (structMap + `≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre` triv + `BaseLoc`-flatness), with `flatModel`/`ofTrivialization`.
- `Core/Algebra/AlgEquiv/Groupoid.lean` — `AlgEquiv.trans_assoc`/`trans_refl`/`refl_trans` (P2.b′), `ext x; rfl`;
  absent in Mathlib v4.29, the cocycle-unblocker.
- `Core/RingTheory/Determinantal/AtlasTransition.lean` — `Algebra.AtlasChart` (chartElt + bare-`k` `trivK`) +
  `AtlasFibreChart` (adds the over-base `fibreModel`) + `overlapTransition` (P2.b); the **2-fold cocycle**
  `overlapTransition_trans_symm`/`_symm` (P2.c) — pure groupoid algebra (Mathlib `self_trans_symm` + the LANDED
  base-side `chartOverlapTransitionK_trans_symm`), no localization-element entry, no kernel-cost trap.
- `Core/RingTheory/Determinantal/LocalTriviality.lean` — **the capstone predicate**
  `Algebra.IsZariskiLocallyTrivialAffineProduct k Base M BaseLoc Fibre U` (P2.d): a chart family
  `ι → AtlasFibreChart` + `cover : (⋃ basicOpen chartElt) = U`. Cocycle = **derived lemma, not a field** (it
  holds for any `AtlasChart`s — storing it would misrepresent the content).
- `Core/FibreZariskiLocalTriviality.lean` — the **DLN instance**
  `reducedFibre_isZariskiLocallyTrivialAffineProduct` over `U = rankROpen` (the open — false over the closure),
  via the new `iUnion_pivotDatum_basicOpen_eq_rankROpen` cover; axiom-clean ⟹ the predicate is satisfiable.

**Boundary re-gate (controller + independent reviewer):** full aggregator GREEN (**3834 jobs**), sorries 0 / 0
axiom, capstone + derived cocycle + new cover lemma all standard-3; both DLN payoffs unchanged.

**Decorrelated review (reviewer + Codex xhigh) — PASS-WITH-NITS** (`threads/p2d-review/verdict.md`): sound +
faithful, no soundness/fidelity defect; cover lemma correct on both inclusions; no global-bundle over-claim. Two
**prose-precision** nits fixed (`60fb928b`):
- **Q2a** — the axiom-clean instance proves the predicate is *satisfiable* (structure inhabited for DLN data),
  NOT that `rankROpen ≠ ∅`; the "non-vacuity / geometric witness / realized" wording was softened to the honest
  inhabited/satisfiable reading (mirrors `FibreBundleHeadline`'s caveat — name=content).
- **Q1c** — the 2-fold cocycle is on the `trivK`/`M` presentation, DECOUPLED from the over-`BaseLoc`
  `fibreModel.triv` product (independent fields); a decoupling line was added so it is not misread as an
  over-base-product cocycle.

## The honest boundary (what is and isn't proved)
- **Proved:** the DLN reduced-fibre bundle is **chartwise** Zariski-locally-trivial over the rank-`=r` open — a
  principal-open cover where each chart's total ring is the over-base product `SchurLoc ⊗_k sweepFibreRing`, flat
  over `SchurLoc`, with the **2-fold** overlap cocycle. The predicate is satisfiable (axiom-clean DLN instance).
- **NOT claimed:** that `rankROpen` is nonempty (no `∃ P ∈ rankROpen`); a **global** `Flat π` / scheme fibre
  bundle / triple-overlap descent; a Mathlib `FiberBundle` (topological-only). The **triple cocycle (P2.c′)** is
  genuinely ill-typed without a target-side `awayTriple` object (Codex-confirmed (i)-(iv) sub-build) and is
  roadmapped to the **R1 global-gluing** track — NOT a blocker for the local-triviality predicate.

## Pending at close (operator-gated)
1. **`Base → TotalRing`/`AmbientRing` rename** in the capstone predicate — escalated (signature change; `Base` is
   the total/source ring by AG convention, the fibration base is `BaseLoc`). Controller lean: keep `Base` (bare
   `Algebra` mirror, `[Algebra k Base]` standard reading; docstrings flag it). Operator's call.
2. **Phase-2 PR** `expedition/det-atlas-p2 → dev` — staged (tip pushed; clean 3-way merge, +959/−123 over 9 Lean
   files; ready title/body in the controller signal). Opening/merging operator-gated.
