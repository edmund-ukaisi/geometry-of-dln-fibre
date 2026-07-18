import DLNFibre.DLN.RLCT.Engine.EngineObligations
import DLNFibre.DLN.RLCT.Validate.RegionGlueModelRead
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# `DLNFibre.DLN.RLCT.Engine.RegionGluePerLeaf` — the per-leaf area-formula read

The engine-facing half of `region_glue`'s per-leaf step: given a leaf `l`'s `ChartBridge` data
(measurable bounded `srcBox`, injective/disjoint `divCoord`/`resCoord`, a.e.-injectivity off a null
set, `LeafPullback`, `LeafJacobian`) and the ratio hypotheses (`c' > 0` below half every terminal
exponent), the box integral over the chart IMAGE is finite:

    ∫⁻ A in l.chartMap '' l.srcBox, ofReal (frobSq (prod M A) ^ (-c')) < ⊤.

Route (elder-ratified fork-8 revision): Mathlib's AREA FORMULA
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) on `srcBox ∖ N̄` (null exceptional fibre
discarded), the `LeafJacobian` upper determinant bound + the `LeafPullback` squeeze reducing the
pulled-back integrand to the monomialised model, then the flat-coordinate `model_read_lt_top`
(`RegionGlueModelRead`) after the measure-preserving transport to `Fin (flatDim M) → ℝ`.

The area formula runs on `Params M` directly, consuming `LeafJacobian`'s `Params`-level derivatives;
this needs `volume` on `Params M` to be an additive Haar measure, supplied here (`Params M` is a
finite-dim normed ℝ-space linearly iso to the flat cube via the banked `paramsEquivFlatCLE`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- `BorelSpace (Params M)` (the pi Borel σ-algebra is the norm-topology Borel one); banked as
`instBorelSpaceParams` in `RouteMSJResolution`, re-exposed here to avoid that heavy import. -/
instance instBorelSpaceParamsGlue (M : Fin (L + 1) → ℕ) : BorelSpace (Params M) :=
  inferInstanceAs (BorelSpace (∀ s : Fin L, Fin (M s.castSucc) → Fin (M s.succ) → ℝ))

/-- **`volume` on `Params M` is an additive Haar measure.** `Params M` is a finite-dim normed
ℝ-space; the banked ℝ-linear iso `paramsEquivFlatCLE` to the flat cube `Fin (flatDim M) → ℝ` (whose
Lebesgue `volume` is Haar) pushes Haar-ness back through `ContinuousLinearEquiv.isAddHaarMeasure_map`,
the measure agreeing by the measure-preserving `paramsEquivFlat`. -/
instance instIsAddHaarMeasureParams (M : Fin (L + 1) → ℕ) :
    (volume : Measure (Params M)).IsAddHaarMeasure := by
  have hsymm : ⇑(paramsEquivFlatCLE M).symm = ⇑(paramsEquivFlat M).symm := by
    funext x
    apply (paramsEquivFlat M).injective
    rw [(paramsEquivFlat M).apply_symm_apply, ← paramsEquivFlatCLE_coe,
      (paramsEquivFlatCLE M).apply_symm_apply]
  have hmap : (volume : Measure (Params M))
      = (volume : Measure (Fin (flatDim M) → ℝ)).map (paramsEquivFlatCLE M).symm := by
    rw [hsymm]
    exact ((measurePreserving_paramsEquivFlat M).symm).map_eq.symm
  rw [hmap]
  infer_instance

/-- **`|det|` is multiplicative over composition** (continuous linear self-maps). The chain-rule
determinant split for the factored chart `chartMap = ψ ∘ β`. -/
theorem abs_det_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E) : |(A.comp B).det| = |A.det| * |B.det| := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp, abs_mul,
    ← ContinuousLinearMap.det, ← ContinuousLinearMap.det]

/-- **Flat-cube finiteness of the monomialised leaf model** (the residual base form as an `if`,
matching `residualBaseForm`). `resRank = 0` (bounded unit): the Morse factor is `1`, so the model is
the pure divisor product, reindexed to an all-axis product (`prod_two_family_eq` with empty residual)
and closed by `prod_abs_rpow_cube_lt_top`. `resRank ≥ 1`: exactly `model_read_lt_top`. -/
theorem flat_leaf_model_lt_top {d nd nr : ℕ} (R : ℝ) (hR : 0 < R)
    (dc : Fin nd → Fin d) (rc : Fin nr → Fin d)
    (hdcInj : Function.Injective dc) (hrcInj : Function.Injective rc)
    (hdisj : Disjoint (Set.range dc) (Set.range rc))
    (e : Fin nd → ℝ) (he : ∀ k, -1 < e k)
    (c' : ℝ) (hc' : 0 < c') (hnr : 0 < nr → c' < (nr : ℝ) / 2) :
    ∫⁻ x in cubeBox d R, ENNReal.ofReal ((∏ k, |x (dc k)| ^ (e k))
      * (if nr = 0 then (1 : ℝ) else ∑ i, (x (rc i)) ^ 2) ^ (-c')) < ⊤ := by
  rcases Nat.eq_zero_or_pos nr with h0 | hpos
  · -- bounded unit: the residual factor collapses to `1`
    subst h0
    simp only [reduceIte, Real.one_rpow, mul_one]
    set g : Fin d → ℝ := fun j => ∑ k, if dc k = j then e k else 0 with hgdef
    have hgd : ∀ k₀, g (dc k₀) = e k₀ := fun k₀ => by
      show (∑ k, if dc k = dc k₀ then e k else 0) = e k₀
      rw [Finset.sum_eq_single k₀ (fun k _ hk => if_neg (fun h => hk (hdcInj h)))
          (fun h => absurd (Finset.mem_univ k₀) h), if_pos rfl]
    have hg0 : ∀ j, (∀ k, dc k ≠ j) → g j = 0 := fun j hjd => by
      show (∑ k, if dc k = j then e k else 0) = 0
      exact Finset.sum_eq_zero (fun k _ => if_neg (hjd k))
    have hgpos : ∀ j, -1 < g j := by
      intro j
      by_cases hjd : ∃ k, dc k = j
      · obtain ⟨k, rfl⟩ := hjd; rw [hgd k]; exact he k
      · push_neg at hjd; rw [hg0 j hjd]; norm_num
    have hreindex : ∀ x : Fin d → ℝ, (∏ k, |x (dc k)| ^ (e k)) = ∏ j, |x j| ^ (g j) := fun x => by
      have h := prod_two_family_eq dc rc hdcInj hrcInj hdisj e 0 g hgd (fun i => i.elim0)
        (fun j hjd _ => hg0 j hjd) x
      simpa using h
    rw [setLIntegral_congr_fun (by rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (fun x _ => by rw [hreindex x])]
    exact prod_abs_rpow_cube_lt_top R hR g hgpos
  · simp only [if_neg hpos.ne']
    exact model_read_lt_top R hR hpos dc rc hdcInj hrcInj hdisj e he c' hc' (hnr hpos)

end DLNFibre.DLN.RLCT
