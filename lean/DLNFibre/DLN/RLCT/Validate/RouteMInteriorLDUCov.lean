import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLDUContract

/-!
# `RouteMInteriorLDUCov` — the n-fold null-slice change-of-variables ENGINE (H3, fs-independent)

The reusable, dimension-agnostic change-of-variables (c-o-v) for an LDU-lensed interior chart, the
`NodeAchieverChart.cov` field's content lifted to **arbitrary ambient `N` and a VARIABLE
weighted-axis count**. This generalizes the worked 4-slice `(3,3,3,3)` template `phi3333_cov`
(injective off `{u 0=0}∪{u 1=0}∪{u 4=0}∪{u 9=0}`) to a chart `φ` injective off the pivot plane
`{u p = 0}` together with a FINITE SET `E : Finset (Fin N)` of extra weighted axes (the `(3,3,3,3)`
case is `E = {1,4,9}`).

## The honest dependency surface

The c-o-v identity `∫⁻_{φ '' (V\{u_p=0})} g = ∫⁻_{V\{u_p=0}} ofReal(∏_j |u_j|^{h_j})·g(φ u)` for an
ARBITRARY `g : (Fin N → ℝ) → ℝ≥0∞` is a genuine geometric IMAGE-pushforward. Mathlib closes it via
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, whose hypotheses are EXACTLY:

* **differentiability** — `∀ x, HasFDerivWithinAt φ (D x) (V\{…}) x` (here from a global
  `Differentiable ℝ φ`); and
* **injectivity** — `Set.InjOn φ {u | u_p ≠ 0 ∧ ∀ j ∈ E, u_j ≠ 0}`.

NEITHER is entailed by the absolute-determinant value alone (`|det Dφ| = ∏_j |u_j|^{h_j}`): `fderiv`
returns `0` for a non-differentiable map, so the det value does not certify differentiability, and a
det value never certifies injectivity. The engine below therefore takes BOTH as explicit hypotheses
(`hdiff`, `hinj`) alongside the black-box determinant value (`habsdet`), and discharges the genuine
fs-independent content: the n-fold null-slice add-back (the finite-union nullity of the extra
weighted-axis planes, each `coordZero_null`, via `measure_biUnion_null_iff`).

This is the **engine**; wiring it to the frozen `interiorLDU_cov` (`RouteMInteriorLDUContract`)
requires two facts ABOUT `interiorLDUphi` — its `Differentiable ℝ` and the `InjOn` off the weighted
axes — which are owned by the chart-CONSTRUCTION sub-task (H1, the factor list + map-equality), NOT
recoverable from `interiorLDU_abs_det`. See the module-tail note.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (measure theory + the cited Jacobian c-o-v).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L N : ℕ}

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
sets is null. The n-fold (variable-count) generalization of the `(3,3,3,3)` 3-slice nullity. -/
theorem weightedAxisSlices_null (E : Finset (Fin N)) :
    (volume : Measure (Fin N → ℝ)) (weightedAxisSlices E) = 0 := by
  rw [weightedAxisSlices, ← Finset.set_biUnion_coe,
    measure_biUnion_null_iff E.countable_toSet]
  exact fun j _ => coordZero_null j

/-! ## The n-fold null-slice change-of-variables engine -/

/-- **H3 — the n-fold null-slice change-of-variables ENGINE** (fs-independent, variable
weighted-axis count). For a differentiable self-map `φ` of `Fin N → ℝ` injective off the pivot plane
`{u_p=0}` ∪ the extra weighted-axis planes `{u_j=0 : j ∈ E}`, with absolute Jacobian
`|det Dφ u| = ∏_j |u_j|^{h_j}` (the black-box `habsdet`): the lintegral c-o-v on `V \ {u_p=0}` holds
for any nonneg measurable `g`, adding the extra slices back as a two-sided null contribution.

Generalizes `phi3333_cov` (`E = {1,4,9}`, `N = 27`) to opaque `N` and a variable `E`. Built from
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` on the punctured set
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
  -- measurability of the pieces
  have hpivot_meas : MeasurableSet {x : Fin N → ℝ | x p = 0} :=
    measurableSet_eq_fun (measurable_pi_apply p) measurable_const
  have hSmeas : MeasurableSet S := hV.diff hpivot_meas
  have hEmeas : MeasurableSet Eset := weightedAxisSlices_measurableSet E
  have hSgmeas : MeasurableSet Sg := hSmeas.diff hEmeas
  have hEnull : (volume : Measure (Fin N → ℝ)) Eset = 0 := weightedAxisSlices_null E
  -- the genuine c-o-v on the fully-punctured set `Sg` (where `hinj` applies)
  have hcov : ∫⁻ x in φ '' Sg, g x
      = ∫⁻ u in Sg, ENNReal.ofReal |LinearMap.det (fderiv ℝ φ u).toLinearMap| * g (φ u) := by
    refine lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSgmeas
      (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) ?_ g
    intro x hx y hy hxy
    refine hinj ⟨hx.1.2, fun j hj => ?_⟩ ⟨hy.1.2, fun j hj => ?_⟩ hxy
    · exact fun h => hx.2 (Set.mem_biUnion hj h)
    · exact fun h => hy.2 (Set.mem_biUnion hj h)
  -- substitute the black-box determinant value
  have hcov' : ∫⁻ x in φ '' Sg, g x
      = ∫⁻ u in Sg, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u) := by
    rw [hcov]; refine setLIntegral_congr_fun hSgmeas (fun u _ => ?_)
    rw [habsdet u]
  -- LHS: the extra-slice image is null, so `φ '' S` and `φ '' Sg` agree a.e.
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
  -- RHS: the source extra-slice is null, so the `\ Eset` restriction is a no-op
  have hRHS : ∫⁻ u in Sg, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u)
      = ∫⁻ u in S, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (φ u) := by
    refine setLIntegral_congr (MeasureTheory.diff_ae_eq_self.2 ?_)
    exact measure_mono_null Set.inter_subset_right hEnull
  rw [hLHS, hcov', hRHS]

/-! ## The frozen `interiorLDU_cov` reduction (the wiring contract for H1 / assembly)

The frozen `interiorLDU_cov` (`RouteMInteriorLDUContract`) needs THREE facts about
`interiorLDUphi M ha hN`, none of which is in its signature: the absolute determinant `habsdet`
(supplied by the black-box `interiorLDU_abs_det`, itself H1-gated through
`interiorLDU_factors`/`interiorLDU_map_eq`), the global `Differentiable ℝ` (`hdiff`, from
`composeFold_hasFDerivAt` once H1's factor list lands), and the `InjOn` off the pivot ∪ extra
weighted axes (`hinj`, the opaque-`N` analogue of `phi3333_injOn`'s triangular back-solve — no
general statement exists in the skeleton). NONE follows from the determinant value alone.

The theorem below makes the reduction precise and machine-checked, with ALL THREE as explicit
hypotheses: GIVEN them (for ANY extra-axis set `E`), the engine yields the EXACT frozen
`interiorLDU_cov` conclusion. Its PROOF TERM introduces no sorry (it is a direct application of the
clean-three engine); the theorem's axiom footprint nonetheless inherits `sorryAx` purely through
`interiorLDU_leafH` — the H2 stub the frozen statement TYPE must mention — not through the proof.
Once H2 fills `interiorLDU_leafH` that `sorryAx` vanishes automatically. The `interiorLDU_cov :=
ldu_cov` wiring is gated on H1 banking `hdiff`/`hinj` and on `interiorLDU_abs_det` becoming
sorry-free; at that point this theorem (specialized at the right `E` = the `leafH > 0` extra axes,
pivot excluded) closes it. -/
theorem interiorLDU_cov_of_facts (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) (E : Finset (Fin (routeMAmbient M)))
    (hdiff : Differentiable ℝ (interiorLDUphi M ha hN))
    (habsdet : ∀ u, |LinearMap.det (fderiv ℝ (interiorLDUphi M ha hN) u).toLinearMap|
      = ∏ j, |u j| ^ (interiorLDU_leafH M ha hN j))
    (hinj : Set.InjOn (interiorLDUphi M ha hN)
      {u : Fin (routeMAmbient M) → ℝ | u (structPivot M hN) ≠ 0 ∧ ∀ j ∈ E, u j ≠ 0})
    (V : Set (Fin (routeMAmbient M) → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in interiorLDUphi M ha hN '' (V \ {x | x (structPivot M hN) = 0}), g x
      = ∫⁻ u in V \ {x | x (structPivot M hN) = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (interiorLDU_leafH M ha hN j))
            * g (interiorLDUphi M ha hN u) :=
  ldu_cov_of_differentiable_injOn (interiorLDUphi M ha hN) (structPivot M hN)
    (interiorLDU_leafH M ha hN) E hdiff habsdet hinj V hV g

end DLNFibre.DLN.RLCT
