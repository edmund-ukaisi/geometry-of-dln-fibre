# BUILD STATE — expedition 2026-07-17-aoyagi-engine (phase checkpoint, 2026-07-24)

**Purpose:** make the built state legible without onerous search. What is PROVED (Lean, clean-three),
what is RENDERED (math, verified), what is the RESIDUAL (the `hideal` monument = the next build).
Controller-verified via `#print axioms` where marked ✓.

## The destination (unchanged)
The cite-free learning-coefficient theorem `aoyagi_learning_coefficient_via_engine` (rlct of the
square-Frobenius DLN loss = C/2), via Aoyagi's resolution reproduced as reusable objects.
**Current honest status of the payoff: cite-free (NO Aoyagi/Watanabe axiom) BUT `sorryAx`-via
`exists_coreResolution:311` (the resolution monument). NOT "closed."** Closing = the next build below.
(AxCheck.lean:1390-1414 carries the tracked-open `#print axioms`.)

## PROVED in Lean — clean-three `[propext, Classical.choice, Quot.sound]`

**Combinatorial value (hlb + hattain) — the value engine [✓ #print axioms verified]:**
- `Engine.O5Realization.o5_core_realized` — ∃ leaf, `divExp = minAdm d = cCodim` (= `hattain`).
- `Engine.O5Realization.tStar_realized` / `clearable_of_minimizer` — minimizer is realized (the steering).
- `Engine.minAdm_le_terminalExponents` — every terminal exponent ≥ minAdm (`hlb`).
- `Aoyagi.RecursionAdapter.hlb_hattain_of_atlasRealizesExponents` — GIVEN a geometric atlas realizing the
  exponents, BOTH hlb+hattain follow (the seam, DLN-`d`-shaped, sorry-free).
- Object D: `Engine.divisorMin_eq_cCodim`; `RLCT.minAdm_eq_cCodim`. Cross-checked by thread-12 battery B1–B6.

**Ideal-identity infra (partial) + Objects A/B/C:**
- `Core.Aoyagi.PrincipalInv` (terminal_bezout, principalInv_regionRepresents) — LANDED.
- `Core.Aoyagi.IdealInvariance` (Object A), `ProductResolution` (Object B `two_mul_rlctAt_eq_divisorMin`),
  `MonomialRLCT` (Object C).

**Box-GEOMETRY (L6 charts + L7 cover) — the geometric-atlas MECHANISMS [✓ #print axioms verified]:**
- `DLN.Aoyagi.Corank2GeoAtlas` (corank-2): `coG_hjac` (dom-wide unit≡1 Jacobian), `coShear_covers`
  (coupled box-containment), `covers_coTree` (L7 fold). — the corank-2 MECHANISM GO.
- `DLN.Aoyagi.GeneralGeoAtlas` (general-`d`): `blockShear_covers_of_norm_bound` (box-containment ALL block
  sizes/pivots), `abs_jacDet_geoPath` (multi-step branch hjac unit≡1), `fanOfSteps`/`covers_fanOfSteps`
  (general-depth varying-center fan cover), `fderiv_outerDisp_zero` (CENTERS discharge).
- `DLN.Aoyagi.LeafCoverTiling` (box-inflation cover engine, `covers_subset`) — sorry-free.
- Reuse primitives (general): `Core.Aoyagi.PathAtoms` (`jacDet_blockShear`=1), `BlockBlowup`
  (`jacDet_blockBlowupMap`), `OriginBlowup`.
- **⚠ CAVEAT (rev-render fidelity audit #7):** the box-geometry proves the mechanisms for a SIMPLER object
  (single-term `outerShear` / product-fan) than the FAITHFUL Aoyagi chart (MULTI-term shear = Schur
  cross-term + the Lemma-2 output/input recoords `C'=Q⁻¹C`; pivot-dependent tree). **It is HALF the `res`
  (the box-geometry); it does NOT touch the `hideal`.** Three seams to close for faithful (SEAM 1
  composition order; SEAM 2 multi-term shear w/ C-generic cover — the load-bearing one; SEAM 3 genuine
  pivot-dependent tree) — see geometric-atlas-build-brief.md.

## RENDERED (math) — verified sound by rev-render, NOT yet Lean
`theory/aoyagi-2023-reproduction/ideal-route-full-render.md` — the ideal-route close-out: **L-A** (Schur
block-elimination ideal identity, any corank), **L-B** (the `b`-chain maintenance), **Theorem 4** (deepest
point), the value bounds. rev-render (7 audit rounds + Codex) verified the SPINE (L-A/L-B/Thm-4) sound +
general — **the coupled-maintenance wall that stalled the expedition is DISSOLVED at the math level.** This
is the intellectual achievement. (The render doc's top carries a CURRENT-STATE summary; the sections below
it are the audited history.)

## THE RESIDUAL — the `hideal` monument (= the next build)
The `res`'s `hideal` (per-chart ideal identity `⟨coreGen∘g⟩=⟨diag b⟩`, a MANDATORY `Chart` field) is
UNBUILT in the ideal route. In Lean it is STILL the geometric-fold monument, resting on sorried leaves:
- **THE WALL** — `foldResid_case11_mergeBoostSplit_canon` (`DLN/Aoyagi/MergeBoostSplit.lean:108`):
  REFUTED-AS-STATED on the raw `foldResid`; TRUE on the source-column-cleared residual; pending the **#69
  elder object re-shape**. "Do NOT attempt as stated."
- `realBranch_appendResidDescent` (`MonumentAtlas.lean:1474`) — the cap descent.
- `leaf_stepInv_of_path'` (`MonumentAssembly.lean:48`) — the L5 fold body.
- `leafPath_compactCover` (`MonumentAtlas.lean:1855`) — the L7 coverage tiling (geometric-fold version).
- `lastLayer_clear_preserves` (`MonumentAtlas.lean:1586`) + a `LastLayerWire` sorry.

**NEXT BUILD (option b, operator-chosen 2026-07-24, to be scoped):** build the ideal-route `hideal`
(L-A/L-B Schur clearing, RENDERED) in Lean → the `res`'s ideal identity, **bypassing** the geometric-fold
WALL. Reuse: trunk Schur machinery (`Core.SchurGauge`/`SchurRankZero`/`SchurProductFactor`/
`ChartSchurConnect`/`RingTheory.Determinantal.Schur`), `Core.Aoyagi.ConjResolution` (a PROVEN
chart-with-`hideal` template), `Corank2Proto` §4 (matrix bridge `Q1_C1_Q2_eq_diag`, on
`expedition/aoyagi-engine-PROTO`). Monument-scale (deep coupled algebra), render-de-risked. Scope first
(actual L-A/L-B Lean size + clean WALL-bypass) before committing.

## Module pointers (where things live)
- Render: `theory/aoyagi-2023-reproduction/ideal-route-full-render.md`. Build brief:
  `expeditions/2026-07-17-aoyagi-engine/geometric-atlas-build-brief.md`.
- Verified Lean: `DLN.Aoyagi.{Corank2GeoAtlas, GeneralGeoAtlas, LeafCoverTiling, RecursionAdapter}`,
  `DLN.RLCT.Engine.O5Realization`, `Core.Aoyagi.{PrincipalInv, IdealInvariance, MonomialRLCT, ConjResolution,
  PathAtoms, BlockBlowup, OriginBlowup}`.
- Residual monument: `DLN.Aoyagi.{MonumentAtlas, MonumentAssembly, MergeBoostSplit, CanonShear}`.
- Axiom truth: `DLN.RLCT.AxCheck.lean` (tracked-open prints at :1390-1414).
- Kept reuse branches: `-L7cover` (merged), `-PROTO` (Corank2Proto §4), `formalise/geometric-atlas`
  (OriginBlowup — superseded by trunk). Dead-branch registry: `map/dead-branch-registry.md`.
