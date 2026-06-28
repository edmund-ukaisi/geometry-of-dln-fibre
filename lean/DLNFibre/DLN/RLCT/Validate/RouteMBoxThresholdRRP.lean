import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRecStepP

/-!
# `RouteMBoxThresholdRRP` — the ∀p depth-2 `(r,r,p)` family `hbox` discharge

The output-width-`p` generalisation of `RouteMBoxThresholdRR4`: the carve-based discharge of the named
gap `RouteMBoxThresholdFinite (![r,r,p])` for the depth-2 `(r,r,p)` family, ALL `r` and ALL `p`. The
two-matrix core `prod (![r,r,p]) A = A0·A1` (`A0 : r×r`, `A1 : r×p`) is exactly the `SchurCore p r` shape
(`Δ` square `r×r`, `S` the free `r×p` block), so the box integral is `SchurCore p r c' 1`, finite below
`schurLambdaP p r = ½·minAdm(![r,r,p])` by `core_schurGen_lt_top (p) (schurLambdaP p) … (schurRecStep_p p)`.

## The threshold match (free)

`schurLambdaP p r := minAdm(![r,r,p])/2` by definition, so `½·minAdm(![r,r,p]) = schurLambdaP p r` is `rfl`
— the gate fires up to EXACTLY the SchurCore-chain threshold, no `minAdm_rr4_eq`-style arithmetic needed.

## Scope / dependency

This is the **#146 deliverable** (the `(r,r,p)` ∀p R1-UPPER leg). It rides only the per-corank dispatch
`schurRecStep_p` (no `monomial_rlct`, no new axiom). `schurRecStep_p`'s cap-B (`t = 0` binding stratum,
`r ≥ 3`) is `schurCoreP_directMorse` — real and axiom-clean; its cap-A (interior stratum) + corank-leaf
branch is `schurCoreP_capA`, now CLOSED (sorry-free, clean-three). So `routeMBoxThresholdFinite_rrp` is
FULLY sorry-free: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `monomial_rlct`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The depth-2 layer reshape `eParamsRRP r p` (`4 → p` of `eParamsRR4`) -/

/-- The `Fin 1` tail family after peeling layer `0` (the layer-`1` fiber `r×p`) of `(![r,r,p])`. -/
abbrev TailFamRRP (r p : ℕ) : Fin 1 → Type :=
  fun s : Fin 1 => Fin ((![r, r, p] : Fin 3 → ℕ) ((0 : Fin 2).succAbove s).castSucc) →
    Fin ((![r, r, p] : Fin 3 → ℕ) ((0 : Fin 2).succAbove s).succ) → ℝ

/-- **The `Params (![r,r,p])` split into the two layer matrix boxes, in `(A0, A1)` order.** Peel layer
`0` (the `r×r` A0) then collapse the singleton `Fin 1` tail (the `r×p` A1) via `piUnique`. An MP reshape
with components `(eParamsRRP r p A).1 = A 0`, `.2 = A 1` (both definitional). The `4 → p` generalisation
of `eParamsRR4`. -/
noncomputable def eParamsRRP (r p : ℕ) :
    Params (![r, r, p] : Fin 3 → ℕ) ≃ᵐ (Fin r → Fin r → ℝ) × (Fin r → Fin p → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun s : Fin 2 => Fin ((![r, r, p] : Fin 3 → ℕ) s.castSucc) →
        Fin ((![r, r, p] : Fin 3 → ℕ) s.succ) → ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piUnique (TailFamRRP r p)))

theorem measurePreserving_eParamsRRP (r p : ℕ) :
    MeasurePreserving (eParamsRRP r p) (volume : Measure (Params (![r, r, p] : Fin 3 → ℕ))) volume := by
  unfold eParamsRRP
  refine (volume_preserving_piFinSuccAbove _ 0).trans ?_
  have hp := (MeasurePreserving.id (volume : Measure (Fin r → Fin r → ℝ))).prod
    (volume_preserving_piUnique (TailFamRRP r p))
  rw [show (volume : Measure ((Fin r → Fin r → ℝ) × (Fin r → Fin p → ℝ)))
    = volume.prod volume from rfl]
  exact hp

/-- `eParamsRRP r p ⁻¹' (matBox r r 1 ×ˢ matBox r p 1) = paramsBoxM (![r,r,p]) 1`. -/
theorem eParamsRRP_preimage_box (r p : ℕ) :
    eParamsRRP r p ⁻¹' (matBox r r 1 ×ˢ matBox r p 1) = paramsBoxM (![r, r, p] : Fin 3 → ℕ) 1 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBoxM, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, h1⟩ s i j
    fin_cases s
    · exact h0 i j
    · exact h1 i j
  · intro h
    exact ⟨fun i j => h 0 i j, fun i j => h 1 i j⟩

/-- **Generic `L = 2` layer-product entry form** `(prod M A) i j = ∑ₖ A₀ᵢₖ·A₁ₖⱼ` (re-derived locally,
the `prodAux` dependent-`Fin`-cast closer; `4 → p` of `prod_two_layer_rr4`). -/
theorem prod_two_layer_rrp (M : Fin 3 → ℕ) (A : Params M) (i : Fin (M 0)) (j : Fin (M 2)) :
    prod M A i j = ∑ k : Fin (M 1), A 0 i k * A 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k using 2

/-- The integrand identity: `frobSq (prod (![r,r,p]) A) = frobSq (rmatMul A0 A1)` (`4 → p` of
`frobSq_prod_eq_eParamsRR4`). -/
theorem frobSq_prod_eq_eParamsRRP (r p : ℕ) (A : Params (![r, r, p] : Fin 3 → ℕ)) :
    frobSq (prod (![r, r, p] : Fin 3 → ℕ) A)
      = frobSq (rmatMul (eParamsRRP r p A).1 (eParamsRRP r p A).2) := by
  change frobSq (prod (![r, r, p] : Fin 3 → ℕ) A) = frobSq (rmatMul (A 0) (A 1))
  unfold frobSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [show prod (![r, r, p] : Fin 3 → ℕ) A i j
      = rmatMul (fun i k => A 0 i k) (fun k j => A 1 k j) i j from by
    rw [prod_two_layer_rrp (![r, r, p] : Fin 3 → ℕ) A i j]; rfl]

theorem measurableSet_paramsBoxM_rrp (r p : ℕ) :
    MeasurableSet (paramsBoxM (![r, r, p] : Fin 3 → ℕ) 1) :=
  measurableSet_paramsBoxM (![r, r, p] : Fin 3 → ℕ) 1

/-- **The reshape identity** `routeMLayerBoxIntegral (![r,r,p]) c' 1 = ∫_{A0∈matBox r r 1}∫_{A1∈matBox r p
1} frobSq(A0·A1)^{−c'}` (`4 → p` of `routeMLayerBoxIntegral_rr4_eq`). -/
theorem routeMLayerBoxIntegral_rrp_eq (r p : ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral (![r, r, p] : Fin 3 → ℕ) c' 1
      = ∫⁻ A0 in matBox r r 1, ∫⁻ A1 in matBox r p 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) := by
  rw [routeMLayerBoxIntegral]
  have hmpP := measurePreserving_eParamsRRP r p
  have hstep3 : ∫⁻ A in paramsBoxM (![r, r, p] : Fin 3 → ℕ) 1,
        ENNReal.ofReal (frobSq (prod (![r, r, p] : Fin 3 → ℕ) A) ^ (-c'))
      = ∫⁻ q in (matBox r r 1 ×ˢ matBox r p 1),
          ENNReal.ofReal ((frobSq (rmatMul q.1 q.2)) ^ (-c')) := by
    have hpre := hmpP.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding (eParamsRRP r p))
      (fun q : (Fin r → Fin r → ℝ) × (Fin r → Fin p → ℝ) =>
        ENNReal.ofReal ((frobSq (rmatMul q.1 q.2)) ^ (-c')))
      (matBox r r 1 ×ˢ matBox r p 1)
    calc ∫⁻ A in paramsBoxM (![r, r, p] : Fin 3 → ℕ) 1,
            ENNReal.ofReal (frobSq (prod (![r, r, p] : Fin 3 → ℕ) A) ^ (-c'))
        = ∫⁻ A in eParamsRRP r p ⁻¹' (matBox r r 1 ×ˢ matBox r p 1),
            ENNReal.ofReal ((frobSq (rmatMul (eParamsRRP r p A).1 (eParamsRRP r p A).2)) ^ (-c')) := by
          rw [eParamsRRP_preimage_box]
          refine setLIntegral_congr_fun (measurableSet_paramsBoxM_rrp r p) (fun A _ => ?_)
          rw [frobSq_prod_eq_eParamsRRP r p A]
      _ = ∫⁻ q in (matBox r r 1 ×ˢ matBox r p 1),
            ENNReal.ofReal ((frobSq (rmatMul q.1 q.2)) ^ (-c')) := hpre
  rw [hstep3]
  have hmeas : Measurable (fun q : (Fin r → Fin r → ℝ) × (Fin r → Fin p → ℝ) =>
      ENNReal.ofReal ((frobSq (rmatMul q.1 q.2)) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  rw [Measure.volume_eq_prod (Fin r → Fin r → ℝ) (Fin r → Fin p → ℝ),
    setLIntegral_prod _ hmeas.aemeasurable]

/-! ## The threshold match `½·minAdm(![r,r,p]) = schurLambdaP p r` (free, by def) -/

/-- `½·minAdm(![r,r,p]) = schurLambdaP p r` — by definition of `schurLambdaP`. -/
theorem minAdm_rrp_half_eq (r p : ℕ) :
    (minAdm (![r, r, p] : Fin 3 → ℕ) : ℝ) / 2 = schurLambdaP p r := rfl

/-! ## The #146 deliverable: `routeMBoxThresholdFinite_rrp` -/

/-- **The ∀p `(r,r,p)` `hbox` discharge.** `RouteMBoxThresholdFinite (![r,r,p])` for ALL `r, p` — the
layer-product box integral is finite below the geometric threshold `½·minAdm(![r,r,p]) = schurLambdaP p r`.
Assembly: the threshold match (`rfl`) + the reshape (`routeMLayerBoxIntegral_rrp_eq`) to the `SchurCore p
r` two-matrix box, finite by `core_schurGen_lt_top (p) (schurLambdaP p) (schurLambdaP_satisfies_threshold
p) (schurRecStep_p p)`; the `c' = 0` branch is the box-volume bound. The ∀p generalisation of
`routeMBoxThresholdFinite_rr4_of_schurRecStep`. (Rides only `schurRecStep_p`, whose cap-A leaf carve
`schurCoreP_capA` is now CLOSED; the cap-B `schurCoreP_directMorse` it wires in is real. FULLY sorry-free.) -/
theorem routeMBoxThresholdFinite_rrp (r p : ℕ) :
    RouteMBoxThresholdFinite (![r, r, p] : Fin 3 → ℕ) := by
  intro c' hc'
  -- `½·minAdm(![r,r,p]) = schurLambdaP p r`, so `c' < schurLambdaP p r`.
  rw [minAdm_rrp_half_eq r p] at hc'
  rw [routeMLayerBoxIntegral_rrp_eq r p]
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand ^0 = 1, box volume finite.
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hmatvol : ∀ m n : ℕ, (volume (matBox m n 1) : ℝ≥0∞) < ⊤ := by
      intro m n
      have hcpt : IsCompact (matBox m n 1) := by
        have heq : matBox m n 1 = Set.univ.pi (fun _ : Fin m => Set.univ.pi (fun _ : Fin n =>
            Set.Icc (-(1 : ℝ)) 1)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    have hcalc : ∫⁻ A0 in matBox r r 1, ∫⁻ A1 in matBox r p 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
        = volume (matBox r r 1) * volume (matBox r p 1) := by
      calc ∫⁻ A0 in matBox r r 1, ∫⁻ A1 in matBox r p 1,
              ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
          = ∫⁻ _A0 in matBox r r 1, ∫⁻ _A1 in matBox r p 1, (1 : ℝ≥0∞) := by
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A0 _ => ?_)
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A1 _ => ?_)
            rw [hzero]; simp [Real.rpow_zero]
        _ = volume (matBox r r 1) * volume (matBox r p 1) := by
            simp only [setLIntegral_const, one_mul]; rw [mul_comm]
    rw [hcalc]
    exact ENNReal.mul_lt_top (hmatvol r r) (hmatvol r p)
  · -- 0 < c' < schurLambdaP p r: the integral IS `SchurCore p r c' 1`, finite by the dispatch.
    have hsc : SchurCore p r (c' : ℝ) 1 :=
      core_schurGen_lt_top p (schurLambdaP p) (schurLambdaP_satisfies_threshold p)
        (schurRecStep_p p) r (c' : ℝ) hc0 hc' 1 one_pos
    rw [SchurCore] at hsc
    exact hsc

end DLNFibre.DLN.RLCT
