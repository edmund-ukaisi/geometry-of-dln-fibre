# BUILD STATE — expedition 2026-07-17-aoyagi-engine (phase checkpoint, 2026-07-24)

**Purpose:** make the built state legible without onerous search. What is PROVED (Lean, clean-three),
what is RENDERED (math, verified), what is the RESIDUAL (the `hideal` monument = the next build).
Controller-verified via `#print axioms` where marked ✓.

## The destination (unchanged)
The cite-free learning-coefficient theorem `aoyagi_learning_coefficient_via_engine` (rlct of the
square-Frobenius DLN loss = C/2), via Aoyagi's resolution reproduced as reusable objects.
**Current honest status of the payoff: cite-free (NO Aoyagi/Watanabe axiom) BUT `sorryAx`-via
`exists_coreResolution:311` (the resolution monument). NOT "closed."** Closing = the next build below.
(AxCheck.lean:1390-1414 carries the tracked-open `#print axioms`. The cite-free claim rests on the
AxCheck:1393 tracked-open comment + the located `@[cited]` cordon (cartographer-confirmed:
`cited_aoyagi_lower_ax`/`cited_watanabe_upper_ax` in `AoyagiCited.lean`, `cited_local_zeta_pole` in
`Core/Analysis/RLCT/Cited.lean`); RE-VERIFY `#print axioms …via_engine` on the next green build.)

## PROVED in Lean — clean-three `[propext, Classical.choice, Quot.sound]`

**Combinatorial value (hlb + hattain) — the value engine [✓ controller `#print axioms` scratch-verified
clean-three; IN-REPO these are gated TRANSITIVELY (via `hlb_hattain_of_atlasRealizesExponents` in the
AxCheck batch + the geo batches), not by individual gate lines — annotate if re-verifying]:**
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
  - **UPDATE (hcover-probe, 2026-07-24): SEAM-2's box-containment side CLEARED head-on** on the FAITHFUL
    three-support `canonNormalizationOf` (Schur cross-term + layer-(S±1) recoord SUMS): (i) order-2 survives
    the recoord sums (`fderiv(coPhi)(0)=0` exact — bilinear ⟹ no linear part ⟹ centers never bite);
    (ii) `C` = recoord-sum length `= width−cleared−1`, WIDTH-bounded and DECREASING with depth (the
    depth-growth NO-GO does not occur) ⟹ `f=r+C·r²` degree-2, `f^[depth]1` finite. So OBL-1 holds for the
    faithful multi-term chart, not just single-term `outerShear`. SEAM-2's C-generic-cover side = OBL-2 (the
    full-fan residual, route-(a)). Artefact: `threads/pnp-l7coupled/probe_multiterm_order2.py`. See
    next-build-render §9.

## RENDERED (math) — verified sound by rev-render, NOT yet Lean
`theory/aoyagi-2023-reproduction/ideal-route-full-render.md` — the ideal-route close-out: **L-A** (Schur
block-elimination ideal identity, any corank), **L-B** (the `b`-chain maintenance), **Theorem 4** (deepest
point), the value bounds. rev-render (7 audit rounds + Codex) verified the SPINE (L-A/L-B/Thm-4) sound +
general — **the coupled-maintenance wall that stalled the expedition is DISSOLVED at the math level.** This
is the intellectual achievement. (The render doc's top carries a CURRENT-STATE summary; the sections below
it are the audited history.)

## THE RESIDUAL — the `hideal` monument (= the next build)
The `res`'s `hideal` (per-chart ideal identity `⟨coreGen∘g⟩=⟨diag b⟩`, a MANDATORY `Chart` field) is
UNBUILT in the ideal route. In Lean it is STILL the geometric-fold monument. **Cone precision
(cartographer):** the registered summit `aoyagi_learning_coefficient_via_engine`'s LITERAL `sorryAx` cone is
the ONE in-place sorry `exists_coreResolution` (`LearningCoefficient.lean:311`); the geometric-fold monument
below is the cone of the SEPARATE driver `exists_coreResolution_via_monument` (a would-be replacement, not
yet swapped in). **The monument = 17 on-cone sorries across 6 files** (current census 42 = 17 on-cone + 25
fossil) — to be **RETIRED WHOLESALE** (banner + delete) by the ideal-route build, NOT closed leaf-by-leaf.
Representative leaves:
- **THE WALL** — atom `foldResid_case11_mergeBoostSplit_canon` (`DLN/Aoyagi/MergeBoostSplit.lean:108`);
  its CONSUMER node = `case1_preserves_stepInv` (`MonumentAtlas.lean:1542`, L4 case1, tagged ⟨THE WALL⟩ —
  SAME wall at two levels). REFUTED-AS-STATED on the raw `foldResid`; TRUE on the source-column-cleared
  residual; pending the **#69 elder object re-shape**. "Do NOT attempt as stated."
- `realBranch_appendResidDescent` (`MonumentAtlas.lean:1473`) cap; `leaf_stepInv_of_path'`
  (`MonumentAssembly.lean:48`) L5; `leafPath_compactCover` (`MonumentAtlas.lean:1854`) L7;
  `lastLayer_clear_preserves` (`MonumentAtlas.lean:1585`) + `LastLayerWire.lean` (2);
  `canonNormalizationOf_shearWithinCarve` (`CanonShear.lean:132`); + the L3/L6/L8 ledger leaves in
  `MonumentAtlas.lean` (:1382/:1412/:1438/:1502/:1791/:1820/:1881). The 6 files: `MonumentAtlas` (11),
  `MonumentAssembly` (1), `MergeBoostSplit` (1), `CanonShear` (1), `LastLayerWire` (2),
  `LearningCoefficient` (1 = `exists_coreResolution:311`).

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
- Residual monument (6 files, 17 on-cone sorries): `DLN.Aoyagi.{MonumentAtlas (11), MonumentAssembly (1),
  MergeBoostSplit (1), CanonShear (1), LastLayerWire (2)}` + `DLN.Aoyagi.LearningCoefficient` (1 =
  `exists_coreResolution:311`). Object-D/B value roots are `Core.Aoyagi.Resolution.divisorMin_eq_cCodim`
  (Core/Aoyagi/Engine.lean:45) + `Resolution.two_mul_rlctAt_eq_divisorMin` (ProductResolution.lean:590).
- Axiom truth: `DLN.RLCT.AxCheck.lean` (tracked-open prints at :1390-1414).
- Kept reuse branches: `-L7cover` (merged), `-PROTO` (Corank2Proto §4), `formalise/geometric-atlas`
  (OriginBlowup — superseded by trunk). Dead-branch registry: `map/dead-branch-registry.md`.
