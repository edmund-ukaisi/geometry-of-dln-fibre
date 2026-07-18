import DLNFibre.DLN.RLCT.Foundations.S1ScalingBridgeDLN
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Foundations.S1Cover
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `DLNFibre.DLN.RLCT.Engine.RegionGlueGlobalize` — the homogeneity local→global step

The `region_glue` box integral `routeMLayerBoxIntegral M c' 1` (= `∫_{paramsBoxM M 1} F^{-c'}`, with
`F = frobSq(prod M ·)`) is finite as soon as it is finite on ANY strictly-smaller box
`paramsBoxM M ε` (`ε > 0`): the integrand's base `F` is degree-`2L` homogeneous
(`S1ScalingBridgeDLN`), a cone, so the scaling bridge transfers finiteness up to the unit box by the
finite positive factor `ε^{-(flatDim − 2L·c')}`.

This is the boundedness-INDEPENDENT half of the assembly: it consumes the per-cover small-box
finiteness (which the chart cover + per-leaf reads supply) and delivers the unit-box conclusion. The
work happens on the flat coordinates `Fin (flatDim M) → ℝ` (where `volume` is Haar and the scaling
bridge lives); `routeMLayerBoxIntegral_eq_flat` is the measure-preserving transport.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators Pointwise

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The box integral in flat coordinates.** `routeMLayerBoxIntegral M c' T =
∫_{cubeBox (flatDim M) T} flatNodeLoss M ^{-c'}` — the measure-preserving transport through
`paramsEquivFlat` (the box pulls back to the flat cube;
`flatNodeLoss M (paramsEquivFlat A) = frobSq (prod M A)`). -/
theorem routeMLayerBoxIntegral_eq_flat (M : Fin (L + 1) → ℕ) (c' T : ℝ) :
    routeMLayerBoxIntegral M c' T
      = ∫⁻ x in cubeBox (flatDim M) T, ENNReal.ofReal (flatNodeLoss M x ^ (-c')) := by
  have hid : ∀ A : Params M, flatNodeLoss M (paramsEquivFlat M A) = frobSq (prod M A) := by
    intro A
    unfold flatNodeLoss
    rw [(paramsEquivFlat M).symm_apply_apply, dlnLoss_zero_eq_frobSq]
  have hmpF := measurePreserving_paramsEquivFlat M
  have hpre := hmpF.setLIntegral_comp_preimage_emb (paramsEquivFlat M).measurableEmbedding
    (fun x => ENNReal.ofReal (flatNodeLoss M x ^ (-c'))) (cubeBox (flatDim M) T)
  rw [paramsEquivFlat_preimage_paramsBoxM] at hpre
  rw [routeMLayerBoxIntegral, ← hpre]
  refine setLIntegral_congr_fun (measurableSet_paramsBoxM M T) (fun A _ => ?_)
  rw [hid A]

/-- **The cube scales.** `ε • cubeBox N 1 = cubeBox N ε` for `ε > 0` (rescale each coordinate's
`[-1,1]` to `[-ε,ε]`). -/
theorem cubeBox_smul (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ε • cubeBox N 1 = cubeBox N ε := by
  ext x
  simp only [cubeBox, Set.mem_smul_set, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  constructor
  · rintro ⟨a, ha, rfl⟩ i
    have hai := ha i
    rw [Pi.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left hai.1 hε.le; linarith
    · have := mul_le_mul_of_nonneg_left hai.2 hε.le; linarith
  · intro hx
    refine ⟨ε⁻¹ • x, fun i => ?_, ?_⟩
    · have hxi := hx i
      rw [Pi.smul_apply, smul_eq_mul, ← div_eq_inv_mul]
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hε]; linarith [hxi.1]
      · rw [div_le_one hε]; exact hxi.2
    · funext i
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hε), one_mul]

/-- **Homogeneity local→global** (the `region_glue` globalization). If the box integral is finite on
some smaller box `paramsBoxM M ε` (`ε > 0`), it is finite on the unit box: the scaling bridge gives
`routeMLayerBoxIntegral M c' ε = ε^(flatDim M − 2L·c') · routeMLayerBoxIntegral M c' 1`, and the
factor `ε^(…)` is finite and positive. -/
theorem routeMLayerBoxIntegral_lt_top_of_small_box (M : Fin (L + 1) → ℕ) (c' ε : ℝ) (hε : 0 < ε)
    (hsmall : routeMLayerBoxIntegral M c' ε < ⊤) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  have hmeas1 : MeasurableSet (cubeBox (flatDim M) 1) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  -- scaling bridge on the flat cube: ∫_{ε • cube 1} = ε^(N-2Lc') · ∫_{cube 1}
  have hbr := lintegral_flatNodeLoss_smul_bridge M c' ε (cubeBox (flatDim M) 1) hε hmeas1
  rw [cubeBox_smul (flatDim M) ε hε, ← routeMLayerBoxIntegral_eq_flat M c' ε,
    ← routeMLayerBoxIntegral_eq_flat M c' 1] at hbr
  -- hbr : routeMLayerBoxIntegral M c' ε = ofReal(ε^(N-2Lc')) * routeMLayerBoxIntegral M c' 1
  set a : ℝ≥0∞ := ENNReal.ofReal (ε ^ ((flatDim M : ℝ) - (2 * L) * c')) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hε _))
  have haT : a ≠ ⊤ := by rw [ha]; exact ENNReal.ofReal_ne_top
  have hsolve : routeMLayerBoxIntegral M c' 1 = a⁻¹ * routeMLayerBoxIntegral M c' ε := by
    rw [hbr, ← mul_assoc, ENNReal.inv_mul_cancel ha0 haT, one_mul]
  rw [hsolve]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr ha0)) hsmall

/-- **The `c' ≤ 0` corner** (no singularity). For `c' ≤ 0` the integrand `F^{-c'} = F^{|c'|}` is
continuous and hence bounded on the compact box, so the box integral is finite with no ratio
hypothesis — `region_glue`'s easy case (in real use `c' ≥ 0`, but the statement quantifies all
`c' : ℝ`). -/
theorem routeMLayerBoxIntegral_nonpos_lt_top (M : Fin (L + 1) → ℕ) (c' : ℝ) (hc : c' ≤ 0) :
    routeMLayerBoxIntegral M c' 1 < ⊤ := by
  rw [routeMLayerBoxIntegral_eq_flat M c' 1]
  have hcont : Continuous (flatNodeLoss M) :=
    (continuous_dlnLoss M 0).comp (continuous_paramsEquivFlat_symm M)
  have hmeas1 : MeasurableSet (cubeBox (flatDim M) 1) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hcompact : IsCompact (cubeBox (flatDim M) 1) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hne : (cubeBox (flatDim M) 1).Nonempty :=
    ⟨0, by intro i _; simp only [Pi.zero_apply, Set.mem_Icc]; constructor <;> norm_num⟩
  obtain ⟨x0, _, hx0max⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  set C : ℝ := flatNodeLoss M x0 with hC
  have hbound : ∀ᵐ x ∂(volume.restrict (cubeBox (flatDim M) 1)),
      ENNReal.ofReal (flatNodeLoss M x ^ (-c')) ≤ ENNReal.ofReal (C ^ (-c')) := by
    filter_upwards [ae_restrict_mem hmeas1] with x hx
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (dlnLoss_nonneg M 0 _) (hx0max hx) (by linarith))
  calc ∫⁻ x in cubeBox (flatDim M) 1, ENNReal.ofReal (flatNodeLoss M x ^ (-c'))
      ≤ ∫⁻ _ in cubeBox (flatDim M) 1, ENNReal.ofReal (C ^ (-c')) := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (C ^ (-c')) * volume (cubeBox (flatDim M) 1) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
              hcompact.measure_lt_top

end DLNFibre.DLN.RLCT
