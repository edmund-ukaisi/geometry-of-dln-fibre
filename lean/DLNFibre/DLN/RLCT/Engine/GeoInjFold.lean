import DLNFibre.DLN.RLCT.Engine.GeoChart
import DLNFibre.DLN.RLCT.Engine.GeoLeafLedger
import DLNFibre.DLN.RLCT.Engine.PivotInjOn
import DLNFibre.DLN.RLCT.Engine.QNodeCarrier
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoInjFold` — the a.e.-injectivity clause of the ChartBridge discharge

The FIRST of the three remaining geometric `(B)` clauses of `chartBridgeFaithful_buildTree`
(`ChartBridgeFaithful.lean`): for every `geoAtlas` piece `c`,

    ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (c.srcBox \ N).

Finding 6 (compass): a blow-up chart is not injective on its exceptional fibre, but it *is* injective
off a null set. The clause needs a **global** `InjOn` (not the local IFT injectivity the fold-Jacobian
supplies), so the argument is the elementary composition one:

* each per-edge factor `geoChartMapNorm _ g = q.symm ∘ (pivotChart × id) ∘ q ∘ S` is
  **quasi-measure-preserving** (QMP: preimages of null sets are null) and **injective off a null set**
  (the bijective conjugators `q`, `q.symm`, `S` contribute nothing; `pivotChart` is injective off its
  exceptional hyperplane `{u_pivot = 0}`, banked `pivotChart_injOn`);
* both properties are stable under composition (`InjOn` off the accumulated null set
  `Nβ ∪ β⁻¹ Na`, whose second piece is null *because* `β` is QMP), so a fold over `tGeo`/`fannedEdges`
  (mirroring `geoAtlas_leaf_update`) carries them to every leaf `chartMap`.

The crux atom is `pivotChart_quasiMeasurePreserving`: it lives entirely on the Haar-clean
`Fin d → ℝ`. All other maps are continuous-linear equivalences; because `Params M` (a `Matrix` pi)
has no direct `IsAddHaarMeasure`/`BorelSpace` instance, the CLEs touching it are shown QMP by
transport through the measure-preserving flattening `paramsEquivFlat` (`measurePreserving_paramsEquivFlat`).
No Jacobian determinant enters the injectivity argument.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

/-! ## The crux atom: `pivotChart i` is quasi-measure-preserving on `Fin d → ℝ` -/

variable {d : ℕ}

/-- The inverse of `pivotChart i` on the open half `{w | w i ≠ 0}`: the pivot coordinate `i` is free
(`w i`), each other coordinate `k` divides out the pivot (`w k / w i`). It is differentiable on that
open set (division by the nonzero pivot). -/
noncomputable def pivotInv (i : Fin d) (w : Fin d → ℝ) : Fin d → ℝ :=
  fun k => if k = i then w i else w k / w i

@[simp] theorem pivotInv_apply_self (i : Fin d) (w : Fin d → ℝ) : pivotInv i w i = w i := by
  simp [pivotInv]

@[simp] theorem pivotChart_apply_self (i : Fin d) (u : Fin d → ℝ) : pivotChart i u i = u i := by
  simp [pivotChart]

theorem pivotInv_apply_ne (i : Fin d) (w : Fin d → ℝ) {k : Fin d} (hk : k ≠ i) :
    pivotInv i w k = w k / w i := by simp [pivotInv, hk]

theorem pivotChart_apply_ne (i : Fin d) (u : Fin d → ℝ) {k : Fin d} (hk : k ≠ i) :
    pivotChart i u k = u i * u k := by simp [pivotChart, hk]

/-- `pivotChart i` inverts `pivotInv i` where the pivot is nonzero. -/
theorem pivotChart_pivotInv (i : Fin d) {w : Fin d → ℝ} (hw : w i ≠ 0) :
    pivotChart i (pivotInv i w) = w := by
  funext k
  by_cases hk : k = i
  · subst hk; rw [pivotChart_apply_self, pivotInv_apply_self]
  · rw [pivotChart_apply_ne i _ hk, pivotInv_apply_self, pivotInv_apply_ne i _ hk]
    field_simp

/-- `pivotInv i` inverts `pivotChart i` where the pivot is nonzero. -/
theorem pivotInv_pivotChart (i : Fin d) {u : Fin d → ℝ} (hu : u i ≠ 0) :
    pivotInv i (pivotChart i u) = u := by
  funext k
  by_cases hk : k = i
  · subst hk; rw [pivotInv_apply_self, pivotChart_apply_self]
  · rw [pivotInv_apply_ne i _ hk, pivotChart_apply_ne i _ hk, pivotChart_apply_self]
    field_simp

theorem pivotChart_continuous (i : Fin d) : Continuous (pivotChart i) := by
  apply continuous_pi
  intro k
  by_cases hk : k = i
  · simp only [pivotChart, if_pos hk]; exact continuous_apply i
  · simp only [pivotChart, if_neg hk]
    exact (continuous_apply i).mul (continuous_apply k)

theorem pivotChart_measurable (i : Fin d) : Measurable (pivotChart i) :=
  (pivotChart_continuous i).measurable

/-- `pivotInv i` is differentiable off the exceptional hyperplane `{w i = 0}`. -/
theorem pivotInv_differentiableOn (i : Fin d) :
    DifferentiableOn ℝ (pivotInv i) {w : Fin d → ℝ | w i ≠ 0} := by
  refine differentiableOn_pi.mpr (fun k => ?_)
  by_cases hk : k = i
  · simp only [pivotInv, if_pos hk]
    exact (differentiable_apply i).differentiableOn
  · simp only [pivotInv, if_neg hk, div_eq_mul_inv]
    exact ((differentiable_apply k).differentiableOn).mul
      (((differentiable_apply i).differentiableOn).inv (fun w hw => hw))

/-- **The preimage-null atom**: `pivotChart i` sends null sets to null preimages. Split the preimage
at the exceptional hyperplane `{u i = 0}` (null, `pivotChart_exceptional_null`); off it, the preimage
is the image of the null set `Z` under the differentiable inverse `pivotInv i`, hence null
(`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`). No Jacobian determinant. -/
theorem pivotChart_preimage_null (i : Fin d) {Z : Set (Fin d → ℝ)}
    (h0 : volume Z = 0) : volume (pivotChart i ⁻¹' Z) = 0 := by
  have hsplit : pivotChart i ⁻¹' Z ⊆
      (pivotInv i '' (Z ∩ {w | w i ≠ 0})) ∪ {u : Fin d → ℝ | u i = 0} := by
    intro u hu
    simp only [Set.mem_preimage] at hu
    by_cases hui : u i = 0
    · exact Or.inr hui
    · refine Or.inl ⟨pivotChart i u, ⟨hu, ?_⟩, ?_⟩
      · simp only [Set.mem_setOf_eq, pivotChart_apply_self]; exact hui
      · exact pivotInv_pivotChart i hui
  refine measure_mono_null hsplit ?_
  apply measure_union_null
  · have hZU : volume (Z ∩ {w : Fin d → ℝ | w i ≠ 0}) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((pivotInv_differentiableOn i).mono Set.inter_subset_right) hZU
  · exact pivotChart_exceptional_null i

/-- **`pivotChart i` is quasi-measure-preserving** (the crux atom): preimages of null sets are null
(`pivotChart_preimage_null`), so `volume.map (pivotChart i) ≪ volume`. -/
theorem pivotChart_quasiMeasurePreserving (i : Fin d) :
    Measure.QuasiMeasurePreserving (pivotChart i)
      (volume : Measure (Fin d → ℝ)) volume := by
  refine ⟨pivotChart_measurable i, ?_⟩
  refine Measure.AbsolutelyContinuous.mk (fun s hs h0 => ?_)
  rw [Measure.map_apply (pivotChart_measurable i) hs]
  exact pivotChart_preimage_null i h0

/-! ## Continuous-linear equivalences are quasi-measure-preserving (finite-dim, Haar) -/

/-- The `pivotChart`'s ambient split space `(Fin d → ℝ) × (Fin k → ℝ)` carries an additive-Haar
`volume` (product of two pi-Haar measures). The `Matrix`-wrapped `Params M` has no such instance and is
handled by transport through the measure-preserving flattening instead. -/
instance instIsAddHaarMeasureVolumeFinProd {d k : ℕ} :
    (volume : Measure ((Fin d → ℝ) × (Fin k → ℝ))).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

/-- **A continuous linear equivalence between finite-dimensional real spaces is
quasi-measure-preserving**: its pushforward of `volume` is again an additive-Haar measure
(`ContinuousLinearEquiv.isAddHaarMeasure_map`), hence absolutely continuous w.r.t. `volume`
(`absolutelyContinuous_isHaarMeasure`). No determinant enters. -/
theorem cle_quasiMeasurePreserving {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X] [BorelSpace X]
    [(volume : Measure X).IsAddHaarMeasure]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [(volume : Measure Y).IsAddHaarMeasure] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    (e : X ≃L[ℝ] Y) :
    Measure.QuasiMeasurePreserving e (volume : Measure X) volume := by
  refine ⟨e.continuous.measurable, ?_⟩
  haveI : (Measure.map e volume).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map e volume
  exact Measure.absolutelyContinuous_isAddHaarMeasure (Measure.map e volume) volume

end DLNFibre.DLN.RLCT.Engine
