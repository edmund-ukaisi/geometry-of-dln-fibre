# Overlay — codebase-shape (cartographer, curated layer) — the whole Lean tree

*Standing artifact (operator-directed, 2026-07-22). The maintained picture of `lean/DLNFibre` that
spawn-briefs and `scripts/expedition brief` draw from — replacing controller-memory for the
READ-FIRST / floor / reuse lists. Built initial pass @ HEAD post-`fe49afdbe`; maintained at the overlay
triggers (bake integrations, closures, close-phase). Census + import facts are tree-verified; capability
lines curate the [[banked-families]] / [[landmark-cards]] cards to the whole tree. Promoted toward
`lean/` at close.*

---

## 1. THE CLUSTER MAP

Sizes are `find -maxdepth 1` per dir; **sorry counts are the canonical `cd lean && scripts/sorries`
meter** (proof-position only — NOT a raw grep, which counts docstring/`⛔ DO NOT FILL` banner mentions).
Tool total at this pass = **41** (post-redirect-bake `9c51289f4`). **Core is entirely sorry-free
(41.5k lines) — the bedrock floor.**

| cluster | lines / sorry | one-line capability | entry-point results | status |
|---|---|---|---|---|
| **Core/Aoyagi** (21f) | 5642 / **0** | the resolution + ideal-RLCT + monomial engine, network-free | `rlctAt_sumSqFam_eq_of_germ_eq` (IdealInvariance, Obj A); `monomialSumSq_wrlctAt_eq` (MonomialRLCT, Obj C); `Resolution`/`Chart` (ProductResolution) + `rlctAt_sumSqFam_eq_iInf_charts` (AreaFormula/monument-1); `blowupResolution` (OriginBlowup/BlowupResolution); `blockBlowupCoordQuot` (BlockDivision), `blockBlowupMap` (BlockBlowup); `terminal_bezout` + `principalInv_regionRepresents` (PrincipalInv); `bandCount_eq`/`perJCard_eq_paper` (OrderCount) + OrderChain; `divisorMin_eq_cCodim` (Engine); PathAtoms, ConjResolution, WeightedCofactor, StepInvShearChild | LIVE **bedrock** |
| **DLN/Aoyagi** (13f) | 5250 / **16** | the monument + summit + E-lane + adapters | `aoyagi_learning_coefficient_via_engine` + `exists_coreResolution` (LearningCoefficient, summit); the monument (MonumentAtlas: leaves on ONE `IsRealBranch` + the 6 `realBranch_*` derived-lemma stubs, post-bake); `bindingSet_chainHeight_eq_thetaCount` (OrderRealizeAssembly, E-lane root) + OrderBinding/OrderRealize/OrderRealizeSwap/OrderRealizeSortedBox; `hlb_hattain_of_atlasRealizesExponents` (RecursionAdapter, salvage seam); `exists_atlasRealizesExponents_d12` (GeometricAtlasD12); `lambdaCore`/`paperLambdaCore` (ClosedForm, P2); `numTop_d22222_ne_aoyagiPoleOrder` (ThetaOrderDistinction); Case2Delta0/Case2TransportWire (L3) | LIVE **edge** (the 10 sorries = the monument skeleton, on-cone) |
| **DLN/RLCT/Foundations** (41f) | 7869 / **0** | the QIP/λ spine + global-homogeneity | `lambdaCore` (Lambda.lean, ℚ over Fin(L+1)); `admTight`/`admTight_subset_adm`/`clamp_mem_admTight` (AdmTight); `rlctGlobal_comp_homeomorph`/`rlctGlobal_eq_rlctAt_zero_of_homogeneous` (GlobalHomog) | LIVE **bedrock** |
| **Core/Analysis/RLCT** (16f) | 1865 / **0** | the abstract rlctAt/rlctGlobal/germ machinery | `rlctAt` (Local.lean:55 / Global.lean:99), `rlctGlobal` (Global.lean:116), `rlctPair` (Pair.lean) | LIVE **bedrock** |
| **Core (codim/dim/orbit/determinantal)** | (in Core's 0-sorry total) | the earlier-expedition geometry feeding Obj D | `cCodim` (CTheta.lean:160), `qipMin` (CThetaQIP.lean:395); Core/Dimension (Codimension/Catenary/Trdeg/…); Core/RingTheory/Determinantal (Schur/rank-normal-form, 7f/2053L); Core/MinimalPrime (TopDimMinPrimes = θ); Core/AlgebraicGeometry/Group/Orbit (orbit dim, 4f) | LIVE **bedrock** (see Finding F6) |
| **DLN/RLCT/Engine** (43f) | 14138 / **4** | MIXED — live salvaged combinatorics + the RETIRED chart-route parts-bin | LIVE salvage: `DivBirthInv`/`DivBirthInv_conOracle_stepChildren` (DivBirthReach.lean:54), `EngineConstruction` (μ-descent spine), `minAdm_le_terminalExponents`/`o5_core_realized` (the adapter's 4 salvage roots). FOSSIL: ChartBridge*/Geo*/CanonicalResolution/`leafDiagFrob_geoAtlasNorm` (the 5 sorries) | **MIXED** (Finding F4) |
| **DLN/RLCT/Validate** (493f) | 147223 / **18** | the PREDECESSOR half-built lane (+ the live `minAdm` def) | live: `minAdm` (RouteMLayerSplit.lean:51), `minAdm_le_Mval_toNat` (RouteMState). FOSSIL: the 18 sorries (prune list §Frontier) | mostly **FOSSIL** |
| **DLN/RLCT** (top, 4f) | 6233 / **3** | Skeleton (legacy stubs) + the cite + the gate | `cited_aoyagi_lower_ax` (AoyagiCited, the kill-target); `AxCheck` (the batch gate); Skeleton.lean (3 legacy stubs = fossil; bare `aoyagi_learning_coefficient` :1685 ≠ summit) | mixed (gate live, Skeleton fossil) |
| **DLN** (top, 4f) | 931 / **0** | the DLN space + mult map + lossDLN | the `Rep`/`mult`/`lossDLN` definitions | LIVE bedrock |

## 2. THE DEPENDENCY ARTERIES

- **Core NEVER imports DLN** — the floor invariant, tree-verified (0 `import DLNFibre.DLN` under Core/).
  The reusable engine is network-free; the DLN/RLCT application sits above it.
- **The monument** (`DLN/Aoyagi/MonumentAtlas.lean`) ← Core/Aoyagi{`PrincipalInv`, `PathAtoms`,
  `BlockDivision`, `ConjResolution`} + `DLN/Aoyagi/LearningCoefficient`.
- **The E-lane root** (`OrderRealizeAssembly`) ← `DLN/Aoyagi`{`OrderRealize`, `OrderRealizeSwap`,
  `OrderBinding`} + Mathlib. The band arithmetic is Core (`Core/Aoyagi/OrderCount` + `OrderChain`).
- **The summit** (`aoyagi_learning_coefficient_via_engine`) ← Obj B (monument) + `corollary-reduction`
  + `b-value-cov` + Obj D. The value chain takes the resolution + min-attainment as HYPOTHESES.
- **The salvage artery** (INTO the summit path, out of the "retired" dir): `LearningCoefficient` +
  7 Engine modules import `RecursionAdapter`/`EngineConstruction`/`DivBirthReach` — the live salvaged
  combinatorics (C1 boundary: green closure only, never ChartBridge*/Geo*/CanonicalResolution).

## 3. THE REUSE INDEX (which cluster owns which capability — hand these names to a seat)

- ideal-RLCT invariance / germ domination → `Core/Aoyagi/IdealInvariance` (`rlctAt_sumSqFam_eq_of_germ_eq`, weighted twin) + `Waypoint` (junk-0 guard).
- monomial-ideal RLCT (Newton/boxed rule) → `Core/Aoyagi/MonomialRLCT` (`monomialSumSq_wrlctAt_eq`, guarded by `DivChain`).
- resolution record + atlas CoV → `Core/Aoyagi/ProductResolution` (`Resolution`/`Chart`) + `AreaFormula` (`rlctAt_sumSqFam_eq_iInf_charts`, the InjOn-off-null area formula).
- blow-up atoms → `Core/Aoyagi/OriginBlowup` (`blowupResolution`, universal-in-D) + `BlockBlowup`/`BlockDivision` (block-center + exact-division quotient).
- the path invariants → `Core/Aoyagi/PrincipalInv` (`terminal_bezout`, `principalInv_regionRepresents`, `StepInv`/`PrincipalInv`, the M17 `IgnoresCoords`/`Deg1SupportedOn`).
- codim / θ / QIP → `Core/CTheta` (`cCodim`), `Core/CThetaQIP` (`qipMin`), `Core/MinimalPrime` (`TopDimMinPrimes` = θ), `Core/RingTheory/Determinantal` (Schur/rank-normal-form), `Core/Dimension` (Codimension/Catenary/Trdeg). Bridge: `RecursionAdapter.qipMin_eq_minAdm` + `Engine.divisorMin_eq_cCodim`.
- global=local-at-0 for homogeneous losses → `Foundations/GlobalHomog` (network-generic).
- the order/chain-height combinatorics → `Core/Aoyagi/OrderCount` (`bandCount_eq`) + `OrderChain`; the faithful poset count → `DLN/Aoyagi/OrderRealizeAssembly` (`bindingSet_chainHeight_eq_thetaCount`).
- the abstract rlct → `Core/Analysis/RLCT` (`rlctAt`/`rlctGlobal`).

## 4. THE FRONTIER LINE

- **LIVE EDGE** (the expedition's working front): `DLN/Aoyagi/MonumentAtlas` — the redirect BAKED
  (`9c51289f4`, 2026-07-22): the leaves now condition on ONE `IsRealBranch e` hypothesis; the **6
  `realBranch_*` derived-lemma stubs are the new cone members** (`realBranch_centerPin` :892 / `_cover`
  :901 / `_descendView` :911 / `_shearWithinCarve` :920 / `_terminal_edgeδ` :930 / `_multiAffine` :941).
  **L4 `case1_preserves_stepInv` = THE WALL** stands. L8's external geometry proof lives in
  `LeafGeometryWire` (in-flight seat branch, NOT yet on the expedition tree) awaiting the integration
  swap. IN-FLIGHT L6-fix round: an elder-authored pin-TIGHTENING on `ShearWithinCarveRaw`
  (`MonumentAtlas.lean:637`) / `IsRealBranch` — re-renders those two defs + strengthens
  `realBranch_shearWithinCarve`'s conclusion only (NOT pre-applied here; not a census change). The last
  library sorry replaces at the final wiring swap (`LearningCoefficient.lean`).
- **SETTLED BEDROCK** (do not re-open): all of Core (41.5k lines, 0 sorry) — the A/C/D engine, the
  blow-up atoms, the QIP/codim/determinantal/dimension/orbit geometry, `Core/Analysis/RLCT`; plus
  `Foundations` (the λ spine, 0 sorry) and the closed E-lane roots (`OrderRealizeAssembly`,
  AxCheck-rooted `c9a4003fe`).
- **FOSSIL / DO-NOT-ENTER** (`cd lean && scripts/sorries` = the meter; 25 fossil sorries; [[dead-routes]]
  DO-NOT-ENTER register): `DLN/RLCT/Validate` (18 sorries — densest `RouteMInteriorLDUContract` ×9,
  `RouteMSJDeeperFlagCore` ×2, + 7 files ×1); `DLN/RLCT/Engine` RETIRED chart parts (4 sorries —
  GeoAlphaGauge, ClearableReify, CanonicalWitness224, GeoAtlasTransfer, each `⛔ DO NOT FILL`-bannered);
  `DLN/RLCT/Skeleton` (3 legacy stubs). Do not "fix" a fossil. **Caveat: Engine is MIXED — the
  DivBirth/EngineConstruction/adapter salvage is LIVE (Finding F4); prune by module, not by directory.**

## Findings (undocumented cluster / orphaned capability / drift — not just cartography)

- **F1 — CENSUS is the canonical tool.** The meter is `cd lean && scripts/sorries` = **41**
  proof-position sorries post-redirect-bake `9c51289f4` (a raw line-grep OVER-counts — docstring +
  `⛔ DO NOT FILL` banner mentions; and UNDER-counts inline `by sorry`, which only the tool catches).
  Tool-verified split: **DLN/Aoyagi 16** (MonumentAtlas 14 [8 leaves + 6 `realBranch_*` derived-lemma
  stubs] + Case2Delta0 1 + LearningCoefficient 1 — the monument, ON-CONE), **DLN/RLCT/Engine 4**
  (GeoAlphaGauge, ClearableReify, CanonicalWitness224, GeoAtlasTransfer — all RETIRED chart fossils),
  **DLN/RLCT/Validate 18**, **DLN/RLCT/Skeleton 3** (= 16 on-cone + 25 fossil). The redirect bake
  APPLIED the 10→16 delta (frontier updated to post-bake). IN-FLIGHT L6-fix round (pin-tightening on
  `ShearWithinCarveRaw`/`IsRealBranch`) re-renders 2 defs + strengthens 1 conclusion — NOT a census
  change. The on-cone-vs-fossil recount at the M-HYGIENE prune is the navigator's gate-verify.
- **F2 — `ClosedForm` is in `DLN/Aoyagi`, not `Foundations`.** (Controller-memory correction — the QIP
  spine's brief listed it under Foundations.)
- **F3 — the QIP/λ spine is SPREAD, not one cluster:** `cCodim` (Core/CTheta), `qipMin` (Core/CThetaQIP),
  `minAdm` (Validate/RouteMLayerSplit — a LIVE def inside the fossil zone), `lambdaCore` (Foundations/Lambda),
  `paperLambdaCore`/`lambdaCore` (DLN/Aoyagi/ClosedForm). A brief wanting "the QIP spine" must reach into
  three clusters.
- **F4 — `DLN/RLCT/Engine` is MIXED, not uniformly retired.** The live salvaged combinatorics
  (`DivBirthReach`/`DivBirthInv`, `EngineConstruction`, `O5Realization`, the 4 adapter roots) are
  consumed by the summit path via `RecursionAdapter`; the chart-route parts (ChartBridge*/Geo*/…) are the
  fossil. The dead-routes salvage carve-out names this, but the "retired Engine" shorthand elsewhere
  reads as wholly-dead — it is not. Prune by module.
- **F5 — `lambdaCore` is DUPLICATED** (`Foundations/Lambda.lean:82`, ℚ over `Fin(L+1)`, M-indexed;
  `DLN/Aoyagi/ClosedForm.lean:84`, ℚ over `Fin(N+1)`, d-indexed). Likely intentional (M-core vs d-core),
  but the shared name is a reuse-index hazard — a brief must disambiguate by module + index type. Flag
  for a naming-unify pass (folds into the M-HYGIENE unit).
- **F6 — substantial earlier-expedition Core clusters carry capability not in the active card set:**
  `Core/RingTheory/Determinantal` (2053L, Schur/rank), `Core/Dimension` (2245L, codim/catenary/trdeg),
  `Core/MinimalPrime` (843L, θ/TopDimMinPrimes), `Core/AlgebraicGeometry/Group/Orbit` (910L, orbit dim).
  All sorry-free bedrock feeding Obj D; recorded here so a future brief finds them instead of rebuilding.
