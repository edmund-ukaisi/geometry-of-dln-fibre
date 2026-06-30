# Thread `genm-r1lower` — R1-LOWER achiever box-divergence at L=2

**Branch:** `expedition/genm-r1lower` PUSHED to origin @ `cacea45a` (lead-authorized banking, NOT a
PR/merge). The H1 skeleton + SUPERSEDED mark are banked; H2a/H3 branch off this tip. Build green.

## Assembly interface (the final spine wiring I own)

The L=2 achiever spine `routeMCore_box_diverges_achiever_spine` (RouteMAchieverDispatch) has 4 branches:
- `L=0` vacuous, `L=1` clean — DONE in the spine.
- INTERIOR `hInterior : (2≤L) → InteriorDrop M → BoxDiverges M c' ε` — MINE: the in-flight
  `routeMCore_box_diverges_interiorLDU` (H1 core, Route B).
- BOUNDARY-SMEARED `hSmeared : (2≤L) → BoundarySmeared M → BoxDiverges M c' ε` — **LANDED by
  genm-r1smeared (2026-06-30)**, branch `origin/expedition/genm-r1smeared @8ab4419c`. CONSUME via
  `import DLNFibre.DLN.RLCT.Validate.RouteMSmearedHSmearedL2`; pass `hSmeared_L2 M hpos c' hc' ε hε`
  (exact slot type `(2≤2) → BoundarySmeared M → BoxDiverges M c' ε`; clean-three, S2-free). STEP-0
  verified every smeared-L2 M in the spine regime IS the square stratum (no residual case). (Variant
  `hSmeared_L2_apply … hsm` if holding `hsm` directly.)

So once my `hInterior` (interior LDU atom) lands, the L=2 spine closes: spine + my interior atom +
genm-r1smeared's `hSmeared_L2` + structural side-conds (hMpos/hne/hNo) → `routeMCore_box_diverges_achiever`
at L=2 → `layerCover_hdiv` → `cover_ge_div`. The smeared half is DONE; the interior half is the
remaining work.

## Arc of the thread

### STEP-0 gate (mandatory) — FAILED the directed premise, caught a false start
Directed: discharge the interior `hcov` from the landed `interiorDet_leaf_headline_eihd`. Verdict:
**WRONG-VEHICLE** (decoder mismatch + non-monomial shape), corroborated by decorrelated Codex.
The eihd det is the D1-UPPER Jacobian, not the R1-LOWER cov. → [`step0-verdict.md`].
Lead accepted; redirected to option (a) (build the monomial interior chart).

### GATE-FIRST (lead's ask) — bounded-vs-wall on the map-eq + cov over opaque widths
Verdict: **BOUNDED (major), NO WALL** on both risk loci, Codex-corroborated. Key discovery: the
det-side bridge is further along than thread-80 recorded — the **LDU straightening is already banked
∀M** (`RouteMKLens`: `kLDU` + `readK_kLDU_det`, free-K det → diagonal-pivot monomial over opaque
widths). Exponent arithmetic `leafH = radial(minAdm−1) ⊕ per-boundary[(r+c)+2(t−1−i)]` verified
against `(3,3,3,3)`. → [`gate-mapeq-verdict.md`], [`codex/gate-mapeq-wall-{prompt,answer}.md`].

### Chart-choice refinement (surfaced to lead)
The interior chart MUST be the LDU-lensed `phiFlatLDU M (tach M) ha hN (kLDU …)`, NOT the free-K
`phiFlatStructV` of the existing `RouteMInteriorContract` (whose `cov` is provably unsatisfiable for
a `t≥2` K-core — `RouteMFlatLDU` header). The existing free-K interior contract is superseded for the
interior branch.

### H1 SPECIFY milestone — LANDED (green)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDUContract.lean` — builds GREEN (full `lake build`,
8317 jobs). The LDU-lensed `NodeAchieverChart` bundle + the interior box-divergence atom
`routeMCore_box_diverges_interiorLDU` (the dispatch spine's `hInterior`). **Assembly is sorry-free**
(rate `routeMCore_interiorLDUphi`, `leaf_integrand`, the det reduction `interiorLDU_abs_det =
phiTarget_abs_det_of_factored`, the bundle, the divergence wiring). **9 stated-correct `sorry`
obligations** isolated:
- H1 (mine): `interiorLDU_factors`, `interiorLDU_map_eq` (the cast bottleneck).
- H1-internal (mine): `interiorLDU_Ubound`, `interiorLDU_Umeas`, `interiorLDU_image`.
- H2 (commissionable): `interiorLDU_leafH` + `_pivot`, `interiorLDU_det_bookkeeping`. → [`H2-subhand-brief.md`]
- H3 (commissionable): `interiorLDU_cov`. → [`H3-subhand-brief.md`]

### Lead's approval + soundness locks (2026-06-30)
APPROVED, no redirect — LDU-lens is correct AND forced. Locked in:
1. Chart-generic endpoint CONFIRMED: instantiate the existing `routeMCore_box_diverges_of_nodeChart`
   with `phi := phiFlatLDU…kLDU` (the skeleton already does this via `interiorLDUnodeChart`); the
   endpoint theorem does NOT change.
2. SOUNDNESS — verify, don't assume: `interiorLDU_Ubound` (a.e.-positivity transfer through `kLDU`) +
   the rate are soundness-critical (the whole reason free-K died is the vanishing-det unsoundness).
   The deep-fill MUST genuinely discharge them — no assertion. Rate flag CONFIRMED already
   (`routeMCore_phiFlatLDU` at `reparam := kLDU`, no added assumption). Ubound transfer is still to be
   PROVEN (precisely-stated sorry now, must be discharged, not asserted).
3. DONE: marked the free-K `RouteMInteriorContract` header "SUPERSEDED-for-interior".

## Open / next (the multi-tide build)
- **H1-core `fs` pin** = build the per-role split CLEs + conjugate the banked Schur/LDU block-maps:
  `radialFactor` (banked, `|u_p|^{active.card−1}`) + `linearFactor` (banked) exist as `ChartFactor`s,
  but `schurFactor`/`lduFactor`/`chainFactor` are NOT yet conjugated into full-ambient `ChartFactor`s —
  that needs `conjBlockFactor (paramsBlockSplitCLE ρ_role) (schurFrameMap/lduCoreMap) …` with the
  per-role reindex `ρ_role : ChartIdx ≃ Block ⊕ Rest` over opaque widths. THIS is the H1-core build;
  the `gs`/`fs` list + `composeFold_bridge_eq` discharge ride on it. (Per lead's pin-before-fanout: the
  honest `fs` requires this multi-factor decomposition — a monolithic single-factor pin would defeat
  H2b's per-factor det. So the fanout of H2b waits on this; H2a + H3 do not.)
  **VERIFIED (2026-06-30): NO per-role `ChartIdx ≃ Block ⊕ Rest` reindex is banked anywhere** —
  `paramsBlockSplitCLE`/`conjBlockFactor` exist ONLY as machinery (`RouteMConjBlock`/`RouteMRoleCLE`/
  `RouteMFactorMaps`), never instantiated with a real role split.

### ROUTE DECISION (Codex xhigh design consult, [`codex/fs-route-design-{prompt,answer}.md`]): HYBRID = Route B
**Do NOT build the per-role `bridgeCLE`/`conjBlockFactor` reindex tower (Route A) — it is the largest
unbanked cost and is UNNECESSARY.** Use the anchor-style FLAT composite (Route B):
`composeFold [linearFactor Q_M, frameFactor_M, kparam/lens-factor_M, radialFactor]`, with the chart
Jacobian det read FLAT off the block-triangular fderiv (exactly as `phi3333` did: `Frame3333Deriv_det
= (z0)⁵(z9)³(z1z4−z2z3)²` via `BlockTriangular.det`, `Kparam3333Deriv_det = (z1)²`, glued by
`LinearMap.det_comp` — NO per-role CLE). Codex DERIVED: the det telescope needs only each factor's
abs-det at the intermediate point, NOT a `paramsBlockSplitCLE ρ`; `readK_kLDU_det` already turns
`det K_s` into the monomial `∏q_i` flat. Block structure buys "which axis the det lands on", provable
as a FLAT lemma, not a coordinate equivalence.
- **First lemma (the de-risking probe):** `frameFactor_abs_det_flat_kLDU` — the flat frame-factor det
  `= ∏_i |q_{s,i}|^{r_s+c_s}` via `readK_kLDU_det`. Probe at a non-anchor asymmetric case with a genuine
  Schur block + nontrivial LDU pivots (Codex suggests `(3,3,4)`) BEFORE the opaque-width build.
- This replaces the earlier "design the reindex tower" plan — the reindex tower is RULED OUT.
- H1 `interiorLDU_factors` + `interiorLDU_map_eq`: the Params-level layer-op decomposition of
  `phiParamsStruct` (on `kLDU`) into the dependency-ordered Schur/LDU/chain/radial fold +
  `composeFold_bridge_eq` discharge. The CLE-collapse spine (`RouteMBridgeCLE`) + per-factor maps
  (`RouteMFactorMaps`) are banked; the open content is the ordered `gs` list + the per-layer `funext`
  match over opaque `Wext`/`Text` widths (the recurring dependent-`Fin`-cast fight — `lean/CLAUDE.md`).
- H1-internal: `interiorLDU_Umeas`/`interiorLDU_image` both need a **`kLDU`-continuity atom** first
  (`continuous_kLDU`). PROOF NOTE (one attempt, reverted to keep green): the building blocks are easy
  — `kLens` continuous via `LinearMap.continuous_of_finiteDimensional` (the two `matrixSplit` legs) +
  `lduCoreMap` continuous (from `lduCoreMap_hasFDerivAt`). The FRICTION is reducing `kLDU`'s `match` on
  `chartIdxEquiv … q`: plain `rw [kLDU, hq, hframe]` does NOT fire (can't rewrite the `match` scrutinee).
  The fix is the banked-`read*_kLDU` pattern (`simp only [kLDU, Equiv.apply_symm_apply]` per-coordinate,
  case-split the `frameSplitEquiv` summand), or a `kLDU_apply_*` per-role pointwise lemma set first
  (K-slot → `kLens` entry; X/N/E/lift → `x q`), then `continuous_pi`. Bounded; its own focused sub-step.
  `interiorLDU_Ubound` then needs the interior-drop witness transferred through `kLDU` (via
  `achieverUfun_ae_pos`-analog + a `kLDU`-image nonzero witness); `interiorLDU_image` = `continuous_kLDU`
  ⟹ chart continuity + `φ 0 = 0`.

## Files
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDUContract.lean` (NEW, green, 9 stated sorries).
- Verdicts + briefs under `threads/genm-r1lower/`.
