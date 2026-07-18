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

## Remaining (BLOCKED on the F1 boundedness strengthening; interface-coupled)

- Per-leaf `∫_{chartMap '' srcBox} F^{-c'} < ⊤`: area-formula CoV → `∫_{srcBox}
  ∏|u|^{divExp−1−2c'}·baseForm^{-c'}·unit` → enlarge bounded `srcBox` to a product cube → Tonelli
  over divisor × Morse × spectator coordinates. **The analytic reads are BANKED:**
  `RouteMSJRadialPolar.lintegral_Ioc_rpow_lt_top` / `Case222CoverGETail.boxT_coord_rpow_lt_top`
  (monomial 1-D, `−1 < e`), `S1RadialMorse.sumSqND_box_lt_top` (Morse, `c' < resRank/2`). The new
  work is the coordinate-separation Tonelli + the area-formula wrapper — both coupled to the (being
  reshaped) `ChartBridge` field layout.
- Cover assembly: `paramsBoxM M ε ⊆ U ⊆ ⋃ chartMap '' srcBox` (from `ChartBridge` +
  `cubeBox_subset_of_isOpen`) → subadditivity (`lintegral_mono_set` + `lintegral_union_le`) → the
  per-leaf finiteness → `routeMLayerBoxIntegral_lt_top_of_small_box`.
- Final `region_glue` exact-discharge: sequenced by the controller (I do not edit
  `EngineObligations.lean`).

## Cleanup note for the controller

`flatNodeLoss_smul` / `dlnLoss_zero_smul` / `prod_smul_pow` / `measurable_flatNodeLoss` /
`paramsEquivFlat_symm_eq_linear` are FOUNDATIONAL but banked in the heavy
`Validate/D1L2ExplicitCoreProducer.lean`. Consuming them there pulls a large analysis cone into
`RegionGlueGlobalize`. A light `Foundations/` re-home (with `D1L2ExplicitCoreProducer` importing it)
would decouple the globalization from the deepest-gauge chain. Not done unilaterally (D1L2 may be
lane-owned).
