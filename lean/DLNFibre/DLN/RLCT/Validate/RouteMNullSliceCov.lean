import DLNFibre.DLN.RLCT.Validate.Case222Resolution

/-!
# `RouteMNullSliceCov` — the n-fold null-slice change-of-variables ENGINE (chart-agnostic)

The reusable, dimension-agnostic change-of-variables (c-o-v) for an achiever chart: the
`NodeAchieverChart.cov` field's content lifted to arbitrary ambient `N` and a VARIABLE
weighted-axis count. This is the standalone home of `ldu_cov_of_differentiable_injOn` — extracted
from `RouteMInteriorLDUCov` so consumers (the LIVE-leaf `RouteMInteriorLiveContract`) need NOT import
the retired dead-leaf `RouteMInteriorLDUContract`. The engine is fully chart-agnostic (takes `φ`, `p`,
`leafH`, `E` abstractly); only `coordZero_null` + Mathlib's Jacobian c-o-v are used.

The c-o-v identity `∫⁻_{φ '' (V\{u_p=0})} g = ∫⁻_{V\{u_p=0}} ofReal(∏_j |u_j|^{h_j})·g(φ u)` for an
ARBITRARY `g : (Fin N → ℝ) → ℝ≥0∞` is a genuine geometric IMAGE-pushforward. Mathlib closes it via
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, whose hypotheses are EXACTLY differentiability
(`hdiff`) and injectivity (`hinj`); NEITHER is entailed by the abs-det value alone, so both are
explicit hypotheses alongside the black-box determinant `habsdet`. The engine discharges the
fs-independent content: the n-fold null-slice add-back.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (measure theory + the cited Jacobian c-o-v).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {N : ℕ}

/-! ## The extra-weighted-axis slice set + its nullity (the fs-independent, variable-count core) -/

/-- The union of the extra weighted-axis pivot planes `⋃_{j ∈ E} {x | x j = 0}` (the `(3,3,3,3)`
`{x 1=0}∪{x 4=0}∪{x 9=0}` at `E = {1,4,9}`), as a `Set (Fin N → ℝ)`. -/
def weightedAxisSlices (E : Finset (Fin N)) : Set (Fin N → ℝ) :=
  ⋃ j ∈ E, {x : Fin N → ℝ | x j = 0}

/-- `weightedAxisSlices E` is measurable (a finite union of coordinate hyperplanes). -/
theorem weightedAxisSlices_measurableSet (E : Finset (Fin N)) :
    MeasurableSet (weightedAxisSlices E) := by
  refine MeasurableSet.biUnion E.countable_toSet (fun j _ => ?_)
  exact measurableSet_eq_fun (measurable_pi_apply j) measurable_const

/-- **The finite union of extra weighted-axis planes is null** (`volume (⋃_{j∈E} {x_j=0}) = 0`):
each coordinate hyperplane is null (`coordZero_null`), and a finite (hence countable) union of null
sets is null. -/
theorem weightedAxisSlices_null (E : Finset (Fin N)) :
    (volume : Measure (Fin N → ℝ)) (weightedAxisSlices E) = 0 := by
  rw [weightedAxisSlices, ← Finset.set_biUnion_coe,
    measure_biUnion_null_iff E.countable_toSet]
  exact fun j _ => coordZero_null j

/-! ## The n-fold null-slice change-of-variables engine -/

/-- **The n-fold null-slice change-of-variables ENGINE** (chart-agnostic, variable weighted-axis
count). For a differentiable self-map `φ` of `Fin N → ℝ` injective off the pivot plane `{u_p=0}` ∪ the
extra weighted-axis planes `{u_j=0 : j ∈ E}`, with absolute Jacobian `|det Dφ u| = ∏_j |u_j|^{h_j}`
(the black-box `habsdet`): the lintegral c-o-v on `V \ {u_p=0}` holds for any nonneg measurable `g`,
adding the extra slices back as a two-sided null contribution.

Built from `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on the punctured set
`(V\{u_p=0}) \ (⋃_{j∈E}{u_j=0})` (where `hinj` applies), then the null-slice add-back: the source
slice is null (`weightedAxisSlices_null`) and its C¹ image is null
(`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`). -/
theorem ldu_cov_of_differentiable_injOn
    (φ : (Fin N → ℝ) → (Fin N → ℝ)) (p : Fin N) (leafH : Fin N → ℕ) (E : Finset (Fin N))
    (hdiff : Differentiable ℝ φ)
    (habsdet : ∀ u, |LinearMap.det (fderiv ℝ φ u).toLinearMap| = ∏ j, |u j| ^ (leafH j))
    (hinj : Set.InjOn φ {u : Fin N → ℝ | u p ≠ 0 ∧ ∀ j ∈ E, u j ≠ 0})
    (V : Set (Fin N → ℝ)) (hV : MeasurableSet V) (g : (Fin N → ℝ) → ℝ≥0∞) :
    ∫⁻ x in φ '' (V \ {x | x p = 0}), g x
      = ∫⁻ u in V \ {x | x p = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u) := by
  set S := V \ {x : Fin N → ℝ | x p = 0} with hS
  set Eset := weightedAxisSlices E with hEset
  set Sg := S \ Eset with hSg
  have hpivot_meas : MeasurableSet {x : Fin N → ℝ | x p = 0} :=
    measurableSet_eq_fun (measurable_pi_apply p) measurable_const
  have hSmeas : MeasurableSet S := hV.diff hpivot_meas
  have hEmeas : MeasurableSet Eset := weightedAxisSlices_measurableSet E
  have hSgmeas : MeasurableSet Sg := hSmeas.diff hEmeas
  have hEnull : (volume : Measure (Fin N → ℝ)) Eset = 0 := weightedAxisSlices_null E
  have hcov : ∫⁻ x in φ '' Sg, g x
      = ∫⁻ u in Sg, ENNReal.ofReal |LinearMap.det (fderiv ℝ φ u).toLinearMap| * g (φ u) := by
    refine lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSgmeas
      (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) ?_ g
    intro x hx y hy hxy
    refine hinj ⟨hx.1.2, fun j hj => ?_⟩ ⟨hy.1.2, fun j hj => ?_⟩ hxy
    · exact fun h => hx.2 (Set.mem_biUnion hj h)
    · exact fun h => hy.2 (Set.mem_biUnion hj h)
  have hcov' : ∫⁻ x in φ '' Sg, g x
      = ∫⁻ u in Sg, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u) := by
    rw [hcov]; refine setLIntegral_congr_fun hSgmeas (fun u _ => ?_)
    rw [habsdet u]
  have hslice_img_null : (volume : Measure (Fin N → ℝ)) (φ '' (S ∩ Eset)) = 0 := by
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      hdiff.differentiableOn ?_
    exact measure_mono_null Set.inter_subset_right hEnull
  have hLHS : ∫⁻ x in φ '' S, g x = ∫⁻ x in φ '' Sg, g x := by
    refine setLIntegral_congr ?_
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ hslice_img_null
      rintro y ⟨⟨x, hxS, rfl⟩, hy⟩
      by_cases hxE : x ∈ Eset
      · exact ⟨x, ⟨hxS, hxE⟩, rfl⟩
      · exact absurd ⟨x, ⟨hxS, hxE⟩, rfl⟩ hy
    · rw [show φ '' Sg \ φ '' S = ∅ from by
        rw [Set.diff_eq_empty]; exact Set.image_mono Set.diff_subset]
      exact measure_empty
  have hRHS : ∫⁻ u in Sg, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u)
      = ∫⁻ u in S, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u) := by
    refine setLIntegral_congr (MeasureTheory.diff_ae_eq_self.2 ?_)
    exact measure_mono_null Set.inter_subset_right hEnull
  rw [hLHS, hcov', hRHS]

end DLNFibre.DLN.RLCT
