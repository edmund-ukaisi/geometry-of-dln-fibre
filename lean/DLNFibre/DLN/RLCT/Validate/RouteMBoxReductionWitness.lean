import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteM334Ratiofin

/-!
# `RouteMBoxReductionWitness` — `RouteMBoxThresholdFinite` is inhabited (the `(3,3,4)` witness)

The generic box-reduction `RouteMBoxReduction.routeMCore_le_matBox` reduces the hfin integral to the
layer-product box integral `routeMLayerBoxIntegral M c' 1`; the finiteness of THAT integral below
`½·minAdm M` is the named analytic hypothesis `RouteMBoxThresholdFinite M`. This file **shows the
witness in-file** (bedrock: a hypothesis the theory invokes must be exhibited as inhabited, not merely
asserted): the closed `(3,3,4)` chain discharges `RouteMBoxThresholdFinite M334` — so the generic
`routeMCore_threshold_lt_top_of_box` is non-vacuous, and on `M334` it reproduces exactly the banked
`routeMCore_M334_threshold_lt_top`.

The reduction `routeMLayerBoxIntegral M334 c' 1 = ∫_{A0∈box}∫_{A1∈box} frobSq(A0·A1)^{−c'}` is the
same `eParams334`/Tonelli reshape `routeMCore_M334_le_matBox` already performs (here applied to the box
integral directly); the finiteness is the banked `matBox334_blowup_lt_top`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- `routeMLayerBoxIntegral M334 c' 1 = ∫_{A0∈matBox 3 3 1}∫_{A1∈matBox 3 4 1} frobSq(A0·A1)^{−c'}`:
the generic layer-product box integral over `Params M334`, reshaped (via the `eParams334` MP layer
split + Tonelli) to the two per-layer matrix boxes. The `paramsBoxM M334 1` is definitionally
`paramsBox334`, so the reshape is `routeMCore_M334_le_matBox` step 3 applied directly to the box
integral. -/
theorem routeMLayerBoxIntegral_M334_eq (c' : ℝ) :
    routeMLayerBoxIntegral (![3, 3, 4] : Fin 3 → ℕ) c' 1
      = ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) := by
  rw [routeMLayerBoxIntegral]
  -- `paramsBoxM M334 1` is definitionally `paramsBox334` (both = all entries in `[−1,1]`).
  have hbox : paramsBoxM (![3, 3, 4] : Fin 3 → ℕ) 1 = paramsBox334 := rfl
  rw [hbox]
  -- Step 3: transport paramsBox334 via eParams334 (MP) to the two layer matrix boxes (Tonelli'd).
  have hmpP := measurePreserving_eParams334
  have hstep3 : ∫⁻ A in paramsBox334,
        ENNReal.ofReal (frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) ^ (-c'))
      = ∫⁻ p in (matBox 3 3 1 ×ˢ matBox 3 4 1),
          ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')) := by
    have hpre := hmpP.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding eParams334)
      (fun p : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 4 → ℝ) =>
        ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')))
      (matBox 3 3 1 ×ˢ matBox 3 4 1)
    calc ∫⁻ A in paramsBox334,
            ENNReal.ofReal (frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) ^ (-c'))
        = ∫⁻ A in eParams334 ⁻¹' (matBox 3 3 1 ×ˢ matBox 3 4 1),
            ENNReal.ofReal ((frobSq (rmatMul (eParams334 A).1 (eParams334 A).2)) ^ (-c')) := by
          rw [eParams334_preimage_box]
          refine setLIntegral_congr_fun measurableSet_paramsBox334 (fun A _ => ?_)
          rw [frobSq_prod_eq_eParams334 A]
      _ = ∫⁻ p in (matBox 3 3 1 ×ˢ matBox 3 4 1),
            ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')) := hpre
  rw [hstep3]
  -- Tonelli into the iterated integral ∫_{A0}∫_{A1}.
  have hmeas : Measurable (fun p : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 4 → ℝ) =>
      ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  rw [Measure.volume_eq_prod (Fin 3 → Fin 3 → ℝ) (Fin 3 → Fin 4 → ℝ),
    setLIntegral_prod _ hmeas.aemeasurable]

/-- **The `(3,3,4)` witness: `RouteMBoxThresholdFinite M334` holds.** The generic analytic hypothesis is
inhabited by the closed `(3,3,4)` chain: `routeMLayerBoxIntegral M334 c' 1 < ⊤` for
`c' < ½·minAdm M334 = 4` (`c' = 0` trivial volume bound; `0 < c' < 4` reshapes to the two-matrix box and
applies the banked `matBox334_blowup_lt_top`). So `routeMCore_threshold_lt_top_of_box M334 this` is
exactly `routeMCore_M334_threshold_lt_top` — the generic re-pointed theorem reproduces the banked one. -/
theorem routeMBoxThresholdFinite_M334 :
    RouteMBoxThresholdFinite (![3, 3, 4] : Fin 3 → ℕ) := by
  intro c' hc'
  rw [minAdm_M334_eq] at hc'
  have hc4 : (c' : ℝ) < 4 := by linarith
  rw [routeMLayerBoxIntegral_M334_eq]
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand ^0 = 1, box volume finite (the iterated ∫∫ 1 = vol·vol < ⊤).
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hmatvol : ∀ p n : ℕ, (volume (matBox p n 1) : ℝ≥0∞) < ⊤ := by
      intro p n
      have hcpt : IsCompact (matBox p n 1) := by
        have heq : matBox p n 1 = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin n =>
            Set.Icc (-(1 : ℝ)) 1)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    have hvol33 : (volume (matBox 3 3 1) : ℝ≥0∞) < ⊤ := hmatvol 3 3
    have hvol34 : (volume (matBox 3 4 1) : ℝ≥0∞) < ⊤ := hmatvol 3 4
    have hcalc : ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
        = volume (matBox 3 3 1) * volume (matBox 3 4 1) := by
      calc ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
              ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
          = ∫⁻ _A0 in matBox 3 3 1, ∫⁻ _A1 in matBox 3 4 1, (1 : ℝ≥0∞) := by
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A0 _ => ?_)
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A1 _ => ?_)
            rw [hzero]; simp [Real.rpow_zero]
        _ = volume (matBox 3 3 1) * volume (matBox 3 4 1) := by
            simp only [setLIntegral_const, one_mul]; rw [mul_comm]
    rw [hcalc]
    exact ENNReal.mul_lt_top hvol33 hvol34
  · -- 0 < c' < 4: the banked blow-up bridge.
    exact matBox334_blowup_lt_top (c' : ℝ) hc0 hc4

/-- **Consistency: the generic re-pointed theorem reproduces the banked `(3,3,4)` headline.** Feeding the
`M334` witness into `routeMCore_threshold_lt_top_of_box` gives exactly `routeMCore_M334_threshold_lt_top`
— the generic ∀M form is a faithful generalisation (no loss on the validated instance). -/
theorem routeMCore_threshold_lt_top_M334_via_box (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm (![3, 3, 4] : Fin 3 → ℕ) : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd (![3, 3, 4] : Fin 3 → ℕ),
      ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) < ⊤ :=
  routeMCore_threshold_lt_top_of_box (![3, 3, 4] : Fin 3 → ℕ) routeMBoxThresholdFinite_M334 c' hc'

end DLNFibre.DLN.RLCT
