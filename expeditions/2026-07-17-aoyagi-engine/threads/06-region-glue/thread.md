# Thread 06 — region-glue tide (glue-t05)

Seat: formalisation (tide). Branch: `expedition/aoyagi-engine--glue-t05`. Target: discharge
`region_glue`'s sorry (`Engine/EngineObligations.lean`) — the box-integral finiteness assembly.

## Deliverables landed (all green, all clean-three `[propext, Classical.choice, Quot.sound]`)

1. **`Foundations/S1ScalingBridge.lean`** — the one genuinely-new analytic lemma, abstract on
   `Fin N → ℝ` (Mathlib-only, engine-independent):
   - `lintegral_smul_set (h) (ε) (0<ε) (K) (MeasurableSet K) : ∫⁻_{ε•K} h = ε^N · ∫⁻_K (h∘(ε•·))`
     — pure Haar CoV (`map_addHaar_smul` + `Module.finrank_fin_fun` + `lintegral_map_equiv`).
   - `lintegral_rpow_neg_smul_bridge (F) (D) (c' ε) (K) (hFnn) (hhomog) (0<ε) (hK) :`
     `∫⁻_{ε•K} F^{-c'} = ε^((N:ℝ) − D·c') · ∫⁻_K F^{-c'}` — the scaling bridge (homogeneity is the
     only DLN input, passed as `hhomog`).

2. **`Engine/RegionGlueGlobalize.lean`** — the boundedness-INDEPENDENT half of the assembly
   (imports the abstract bridge + banked homogeneity; NOT `EngineObligations`):
   - `routeMLayerBoxIntegral_eq_flat` — MP transport of the box integral to the flat cube
     (`flatNodeLoss M (paramsEquivFlat A) = frobSq (prod M A)`).
   - `cubeBox_smul : ε • cubeBox N 1 = cubeBox N ε`.
   - `lintegral_flatNodeLoss_smul_bridge` — the abstract bridge at `F = flatNodeLoss M`, `D = 2L`,
     consuming the BANKED `flatNodeLoss_smul` (`D1L2ExplicitCoreProducer`) + `dlnLoss_nonneg`.
   - `routeMLayerBoxIntegral_lt_top_of_small_box (M) (c' ε) (0<ε) (hsmall) :`
     finiteness on any `paramsBoxM M ε` ⟹ finiteness on the unit box (the homogeneity local→global).
   - `routeMLayerBoxIntegral_nonpos_lt_top (M) (c') (c'≤0)` — the no-singularity `c'≤0` corner.

## Findings surfaced (STOP-tripwire)

- **F1 (blocking soundness gap).** `region_glue` is NOT provable from the current `ChartBridge`: the
  separated read is valid only on a BOUNDED `srcBox`. Realizable counterexample (`L=1`, `M=(2,1)`,
  `F = y₁²+y₂²`): unbounded sector charts satisfy every `LeafPullback`/`LeafJacobian` clause
  advertising `divExp = a ≥ 3` (so `hrat` allows `c' < a/2`), yet the integral diverges for
  `c' ≥ 1`. **Fix requested:** add per-leaf `MeasurableSet srcBox ∧ ∃ R>0, srcBox ⊆
  paramsEquivFlat⁻¹'(cubeBox (flatDim M) R)` to `ChartBridge`/`CanonicalResolution`. Nonempty
  interior is NOT needed; measurability + boundedness ARE. Decorrelated-Codex-corroborated; feeds the
  elder abstract-field gate (task #56). Artefact: `codex/assembly-arch-{prompt,answer}.md`.
- **F2 (route correction).** The banked transport `rlctAtOn_boundedUnit_localHomeomorph` is
  INAPPLICABLE to the current `LeafJacobian` (it needs `Dψsymm`, openness of `β '' srcBox`, a fixed
  basepoint — none supplied). The per-leaf read is discharged by the **area formula**
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul` on `srcBox \ N` + chain rule `Dφ = Dψ(β·)∘Dβ`,
  `|det| ≤ hi·∏|u|^{divExp−1}`), which needs only the `|det Dψ|` UPPER bound (present). The scaling
  bridge is still used — only for the small-box→unit-box globalization (done), not per-leaf.

## Post-sync (2026-07-18): strengthened ChartBridge PULLED; battery + dedup landed

- Merged `origin/expedition/aoyagi-engine` (ff → `ddd8a8d9d`): per-leaf clause now carries
  `MeasurableSet l.srcBox ∧ ∃ R>0, l.srcBox ⊆ paramsEquivFlat M ⁻¹' cubeBox (flatDim M) R`.
- `map/battery/g-glue-unbounded-srcbox.py` LANDED (exit 0) — the F1 kill witness.
- Dedup: `S1ScalingBridgeDLN` deleted; `RegionGlueGlobalize` consumes banked `flatNodeLoss_smul`.

## BUILD-READY DECOMPOSITION of the per-leaf read (substrate ALL banked; precedent D1HChartResidual)

`leaf_chart_image_lintegral_lt_top` (helper, `0<c'`, consumes ChartBridge per-leaf tuple + hrat):
`∫⁻ A in l.chartMap '' l.srcBox, ofReal(frobSq(prod M A)^{-c'}) < ⊤`.
1. Null-hull: `exists_measurable_superset_of_null N` → measurable null `N'⊇N`; `InjOn chartMap (srcBox\N')`.
2. Split off null image: `chartMap''srcBox = chartMap''(srcBox\N') ∪ chartMap''(srcBox∩N')`;
   `lintegral_union_le`; 2nd = 0 via `setLIntegral_measure_zero` +
   `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (Jacobian.lean:561).
3. Area formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (Jacobian.lean:1189) on `srcBox\N'`
   (MeasurableSet + `HasFDerivWithinAt (ψ∘β)` via `HasFDerivAt.comp` from LeafJacobian + InjOn).
4. Bound integrand: `F∘chartMap=(∏u²)R` [LeafPullback]; `|det(Dψ(β·)∘Dβ)| ≤ hi·∏|u|^{divExp−1}`
   [`ContinuousLinearMap.det_comp` + LeafJacobian]; `R^{-c'} ≤ lo^{-c'}baseForm^{-c'}` [rpow antitone,
   c'>0] ⟹ `≤ hi·lo^{-c'}·∏|u|^{divExp−1−2c'}·baseForm^{-c'}`.
5. Enlarge `srcBox\N' ⊆ paramsEquivFlat⁻¹'(cubeBox R)` [ChartBridge boundedness]; `lintegral_mono_set`;
   transport (MP) to `∫_{cubeBox (flatDim M) R} ∏|x(divCoord k)|^{divExp−1−2c'}·(∑x(resCoord i)²)^{-c'}`.
6. Coordinate-separation Tonelli (THE new plumbing; template = `volume_preserving_piEquivPiSubtypeProd`
   in D1HChartResidual/D1SecondPeelChart): split `Fin (flatDim M)` by `p = (·∈range divCoord)`:
   - divisor block: `prod_rpow_lintegral_Ioo_box_lt_top` (RouteMSJMonomialLower; ±-fold Icc→Ioo),
     needs `divExp k−1−2c' > −1 ⟺ c'<divExp k/2` [hrat].
   - complement: Morse factor depends only on resCoord ⊆ complement → split R vs spectators →
     `sumSqND_box_lt_top` (`c'<resRank/2` [hrat resRank fold]; resRank=0 → factor = cube vol) × spectator vol.

`region_glue_of_chartBridge` (full discharge, controller wires into `region_glue`'s body):
`rcases le_or_lt c' 0` → (`routeMLayerBoxIntegral_nonpos_lt_top`) | (0<c': `hbridge` gives U∋0 [F(0)=0, L≥1],
`cubeBox_subset_of_isOpen` pulled back → `paramsBoxM M ε ⊆ U ⊆ ⋃chartMap''srcBox`,
`lintegral_mono_set` + `lintegral_biUnion_le` over leaves + step-1..6 → `∫_{paramsBoxM M ε}<⊤` →
`routeMLayerBoxIntegral_lt_top_of_small_box`).

NEEDS-vs-FORCES (elder gate #56): all consumed fields have needs ⊆ forces under the strengthened
ChartBridge. Watch item (no gap): step-4 Morse read wants `c'<resRank/2`, covered by the resRank fold
+ `minAdm ≤ resRank`. No third gap identified; image-cover + residualCore-squeeze consumed only as stated.

## Remaining (per-leaf ~300-line Tonelli + cover; substrate fully banked, interface now final)

- Build steps 1–6 as `leaf_chart_image_lintegral_lt_top` + the cover as `region_glue_of_chartBridge`
  (helper form, consuming ChartBridge directly — the ratified hypotheses are on the branch).
- Controller sequences `region_glue := region_glue_of_chartBridge …` after the elder abstract-field gate.

## Cleanup note for the controller

`flatNodeLoss_smul` / `dlnLoss_zero_smul` / `prod_smul_pow` / `measurable_flatNodeLoss` /
`paramsEquivFlat_symm_eq_linear` are FOUNDATIONAL but banked in the heavy
`Validate/D1L2ExplicitCoreProducer.lean`. Consuming them there pulls a large analysis cone into
`RegionGlueGlobalize`. A light `Foundations/` re-home (with `D1L2ExplicitCoreProducer` importing it)
would decouple the globalization from the deepest-gauge chain. Not done unilaterally (D1L2 may be
lane-owned).
