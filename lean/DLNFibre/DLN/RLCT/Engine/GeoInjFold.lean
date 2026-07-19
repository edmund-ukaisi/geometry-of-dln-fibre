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

/-! ## Transport through the flattening: CLEs touching `Params M` are quasi-measure-preserving

`Params M` (a `Matrix` pi) has no `IsAddHaarMeasure`/`BorelSpace` instance, so `cle_quasiMeasurePreserving`
does not apply to CLEs with `Params M` as (co)domain. But `paramsEquivFlat` is measure-preserving
(`measurePreserving_paramsEquivFlat`), and its CLE form has the same underlying map
(`paramsEquivFlatCLE_coe`); conjugating a Params-CLE by it produces a CLE between the clean flat
spaces, whose QMP transports back. -/

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- The flattening CLE is measure-preserving (`measurePreserving_paramsEquivFlat`, transported to the
`ContinuousLinearEquiv` form by the coercion agreement). -/
theorem paramsEquivFlatCLE_measurePreserving (M : Fin (L + 1) → ℕ) :
    MeasurePreserving ⇑(paramsEquivFlatCLE M) (volume : Measure (Params M)) volume := by
  have h := measurePreserving_paramsEquivFlat M
  rwa [← paramsEquivFlatCLE_coe M] at h

/-- The CLE flattening's inverse has the same underlying map as the `MeasurableEquiv`'s inverse (both
are the unique inverse of the shared forward map). -/
theorem paramsEquivFlatCLE_symm_coe (M : Fin (L + 1) → ℕ) :
    ⇑(paramsEquivFlatCLE M).symm = ⇑(paramsEquivFlat M).symm := by
  funext y
  apply (paramsEquivFlat M).injective
  rw [(paramsEquivFlat M).apply_symm_apply, ← paramsEquivFlatCLE_coe M,
    (paramsEquivFlatCLE M).apply_symm_apply]

/-- The flattening CLE is QMP. -/
theorem paramsEquivFlatCLE_qmp (M : Fin (L + 1) → ℕ) :
    Measure.QuasiMeasurePreserving ⇑(paramsEquivFlatCLE M) (volume : Measure (Params M)) volume :=
  (paramsEquivFlatCLE_measurePreserving M).quasiMeasurePreserving

/-- The inverse flattening CLE is QMP (`MeasurableEquiv.quasiMeasurePreserving_symm`, transported
through the coe agreement and `map_eq`). -/
theorem paramsEquivFlatCLE_symm_qmp (M : Fin (L + 1) → ℕ) :
    Measure.QuasiMeasurePreserving ⇑(paramsEquivFlatCLE M).symm
      (volume : Measure (Fin (flatDim M) → ℝ)) (volume : Measure (Params M)) := by
  have h := MeasurableEquiv.quasiMeasurePreserving_symm (volume : Measure (Params M))
    (paramsEquivFlat M)
  rw [(measurePreserving_paramsEquivFlat M).map_eq] at h
  rwa [paramsEquivFlatCLE_symm_coe M]

/-- **A CLE with `Params M` as domain is QMP** (clean codomain): conjugate by the flattening. -/
theorem cle_qmp_of_params_dom {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y] [BorelSpace Y]
    [(volume : Measure Y).IsAddHaarMeasure] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    (e : Params M ≃L[ℝ] Y) :
    Measure.QuasiMeasurePreserving (⇑e) (volume : Measure (Params M)) volume := by
  have hcomp := (cle_quasiMeasurePreserving ((paramsEquivFlatCLE M).symm.trans e)).comp
    (paramsEquivFlatCLE_qmp M)
  have hEq : ⇑((paramsEquivFlatCLE M).symm.trans e) ∘ ⇑(paramsEquivFlatCLE M) = ⇑e := by
    funext w
    simp only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  rwa [hEq] at hcomp

/-- **A CLE with `Params M` as codomain is QMP** (clean domain): conjugate by the flattening. -/
theorem cle_qmp_of_params_cod {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X] [BorelSpace X]
    [(volume : Measure X).IsAddHaarMeasure] [LocallyCompactSpace X] [SecondCountableTopology X]
    (e : X ≃L[ℝ] Params M) :
    Measure.QuasiMeasurePreserving (⇑e) (volume : Measure X) (volume : Measure (Params M)) := by
  have hcomp := (paramsEquivFlatCLE_symm_qmp M).comp
    (cle_quasiMeasurePreserving (e.trans (paramsEquivFlatCLE M)))
  have hEq : ⇑(paramsEquivFlatCLE M).symm ∘ ⇑(e.trans (paramsEquivFlatCLE M)) = ⇑e := by
    funext w
    simp only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  rwa [hEq] at hcomp

/-- **A CLE `Params M ≃L Params M` is QMP**: conjugate both ends by the flattening. -/
theorem cle_qmp_of_params_both (e : Params M ≃L[ℝ] Params M) :
    Measure.QuasiMeasurePreserving (⇑e) (volume : Measure (Params M)) volume := by
  have hcomp := ((paramsEquivFlatCLE_symm_qmp M).comp
    (cle_quasiMeasurePreserving
      ((paramsEquivFlatCLE M).symm.trans (e.trans (paramsEquivFlatCLE M))))).comp
    (paramsEquivFlatCLE_qmp M)
  have hEq : (⇑(paramsEquivFlatCLE M).symm ∘
      ⇑((paramsEquivFlatCLE M).symm.trans (e.trans (paramsEquivFlatCLE M)))) ∘
      ⇑(paramsEquivFlatCLE M) = ⇑e := by
    funext w
    simp only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  rwa [hEq] at hcomp

/-! ## The composition step and the per-factor properties -/

/-- **The a.e.-injectivity composition step**: if `f` is QMP and both `f`, `g` are injective off a null
set, then `g ∘ f` is injective off the accumulated null set `Nf ∪ f⁻¹ Ng` (the second piece is null
*because* `f` is QMP — this is where `preimage_null` is used). -/
theorem comp_ae_injOn {α β γ : Type*} [MeasureSpace α] [MeasureSpace β]
    {f : α → β} {g : β → γ}
    (hfQMP : Measure.QuasiMeasurePreserving f volume volume)
    (hf : ∃ N : Set α, volume N = 0 ∧ Set.InjOn f (Set.univ \ N))
    (hg : ∃ N : Set β, volume N = 0 ∧ Set.InjOn g (Set.univ \ N)) :
    ∃ N : Set α, volume N = 0 ∧ Set.InjOn (g ∘ f) (Set.univ \ N) := by
  obtain ⟨Nf, hNf0, hNfInj⟩ := hf
  obtain ⟨Ng, hNg0, hNgInj⟩ := hg
  refine ⟨Nf ∪ f ⁻¹' Ng, measure_union_null hNf0 (hfQMP.preimage_null hNg0), ?_⟩
  intro x hx y hy hxy
  rw [Set.mem_diff] at hx hy
  obtain ⟨-, hxN⟩ := hx
  obtain ⟨-, hyN⟩ := hy
  rw [Set.mem_union, not_or, Set.mem_preimage] at hxN hyN
  obtain ⟨hxNf, hxNg⟩ := hxN
  obtain ⟨hyNf, hyNg⟩ := hyN
  have hfeq : f x = f y :=
    hNgInj ⟨Set.mem_univ _, hxNg⟩ ⟨Set.mem_univ _, hyNg⟩ hxy
  exact hNfInj ⟨Set.mem_univ _, hxNf⟩ ⟨Set.mem_univ _, hyNf⟩ hfeq

/-- A bijective map (given as a `Function.Injective` witness) is injective off the null set `∅`. -/
theorem ae_injOn_of_injective {α β : Type*} [MeasureSpace α] {f : α → β}
    (hf : Function.Injective f) : ∃ N : Set α, volume N = 0 ∧ Set.InjOn f (Set.univ \ N) :=
  ⟨∅, measure_empty, hf.injOn⟩

/-! ### `Prod.map (pivotChart i) id` is QMP and injective off its exceptional hyperplane -/

/-- `Prod.map (pivotChart i) id` is QMP on the split space (`Measure.map_prod_map` + AC of the product,
using `pivotChart_quasiMeasurePreserving`). -/
theorem pivotChart_prod_qmp {d k : ℕ} (i : Fin d) :
    Measure.QuasiMeasurePreserving (Prod.map (pivotChart i) (id : (Fin k → ℝ) → Fin k → ℝ))
      (volume : Measure ((Fin d → ℝ) × (Fin k → ℝ))) volume := by
  refine ⟨(pivotChart_measurable i).prodMap measurable_id, ?_⟩
  rw [Measure.volume_eq_prod,
    ← Measure.map_prod_map _ _ (pivotChart_measurable i) measurable_id]
  exact (pivotChart_quasiMeasurePreserving i).absolutelyContinuous.prod
    (Measure.QuasiMeasurePreserving.id volume).absolutelyContinuous

/-- `Prod.map (pivotChart i) id` is injective off the null hyperplane `{p | p.1 i = 0}` (the first
factor is `pivotChart_injOn` off `{u i = 0}`, the second is the identity). -/
theorem pivotChart_prod_ae_injOn {d k : ℕ} (i : Fin d) :
    ∃ N : Set ((Fin d → ℝ) × (Fin k → ℝ)), volume N = 0 ∧
      Set.InjOn (Prod.map (pivotChart i) (id : (Fin k → ℝ) → Fin k → ℝ)) (Set.univ \ N) := by
  refine ⟨{p | p.1 i = 0}, ?_, ?_⟩
  · have hset : {p : (Fin d → ℝ) × (Fin k → ℝ) | p.1 i = 0}
        = {u : Fin d → ℝ | u i = 0} ×ˢ (Set.univ : Set (Fin k → ℝ)) := by
      ext p; simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, pivotChart_exceptional_null i, zero_mul]
  · intro p hp p' hp' hpp
    rw [Set.mem_diff] at hp hp'
    simp only [Set.mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
    obtain ⟨u, v⟩ := p; obtain ⟨u', v'⟩ := p'
    simp only [Prod.map, id_eq, Prod.mk.injEq] at hpp
    exact Prod.ext (pivotChart_injOn i hp hp' hpp.1) hpp.2

/-! ### The blow-up conjugators `qNodeOf`, `flatSwapCLE` are QMP -/

/-- The per-node center split `qNodeOf` is QMP (it is `qOfCenterCLE`, a CLE `Params M ≃L product`). -/
theorem qNodeOf_qmp (node : StepData M) (hd : dCenterOfNode M node ≤ flatDim M) :
    Measure.QuasiMeasurePreserving ⇑(qNodeOf M node hd) (volume : Measure (Params M)) volume := by
  have hcoe : ⇑(qNodeOf M node hd)
      = ⇑(qOfCenterCLE M (cNodeOf M node hd) (cNodeOf_injective M node hd)) :=
    qOfCenter_coe_cle M _ _
  rw [hcoe]; exact cle_qmp_of_params_dom _

/-- The inverse per-node center split `(qNodeOf).symm` is QMP. -/
theorem qNodeOf_symm_qmp (node : StepData M) (hd : dCenterOfNode M node ≤ flatDim M) :
    Measure.QuasiMeasurePreserving ⇑(qNodeOf M node hd).symm volume (volume : Measure (Params M)) := by
  have hcoe : ⇑(qNodeOf M node hd).symm
      = ⇑(qOfCenterCLE M (cNodeOf M node hd) (cNodeOf_injective M node hd)).symm := rfl
  rw [hcoe]; exact cle_qmp_of_params_cod _

/-- The diagonal-normalization source swap `flatSwapCLE` is QMP. -/
theorem flatSwapCLE_qmp (p d : Fin (flatDim M)) :
    Measure.QuasiMeasurePreserving ⇑(flatSwapCLE M p d) (volume : Measure (Params M)) volume :=
  cle_qmp_of_params_both (flatSwapCLE M p d)

/-! ### The per-factor properties of `geoChartMapNorm (fun _ => id) g` -/

/-- **Each per-edge factor is QMP**: off-cone it is `id`; on-cone it is
`q.symm ∘ (pivotChart × id) ∘ q ∘ S`, a composition of QMP maps. -/
theorem geoChartMapNorm_id_qmp (g : GeoChart M) :
    Measure.QuasiMeasurePreserving (geoChartMapNorm (fun _ => id) g)
      (volume : Measure (Params M)) volume := by
  obtain ⟨node, edge, pivot⟩ := g
  by_cases hd : dCenterOfNode M node ≤ flatDim M
  · by_cases hp : pivot < dCenterOfNode M node
    · rw [geoChartMapNorm_id_on_cone node edge pivot hd hp]
      exact (((qNodeOf_symm_qmp node hd).comp
        ((pivotChart_prod_qmp ⟨pivot, hp⟩).comp (qNodeOf_qmp node hd)))).comp
        (flatSwapCLE_qmp _ _)
    · simp only [geoChartMapNorm, dif_pos hd, dif_neg hp]
      exact Measure.QuasiMeasurePreserving.id volume
  · simp only [geoChartMapNorm, dif_neg hd]
    exact Measure.QuasiMeasurePreserving.id volume

/-- **Each per-edge factor is injective off a null set**: off-cone it is `id` (null set `∅`); on-cone
it is `q.symm ∘ (pivotChart × id) ∘ q ∘ S` with `q`, `q.symm`, `S` bijective and the middle factor
injective off its exceptional hyperplane, so `comp_ae_injOn` accumulates the null set. -/
theorem geoChartMapNorm_id_ae_injOn (g : GeoChart M) :
    ∃ N : Set (Params M), volume N = 0 ∧
      Set.InjOn (geoChartMapNorm (fun _ => id) g) (Set.univ \ N) := by
  obtain ⟨node, edge, pivot⟩ := g
  by_cases hd : dCenterOfNode M node ≤ flatDim M
  · by_cases hp : pivot < dCenterOfNode M node
    · rw [geoChartMapNorm_id_on_cone node edge pivot hd hp]
      -- β = q.symm ∘ (pivotChart × id) ∘ q ∘ S
      have hqS := comp_ae_injOn (flatSwapCLE_qmp _ _)
        (ae_injOn_of_injective (flatSwapCLE M (cNodeOf M node hd ⟨pivot, hp⟩)
          (diagTargetOf M node edge (by omega))).injective)
        (ae_injOn_of_injective (qNodeOf M node hd).injective)
      have hPqS := comp_ae_injOn ((qNodeOf_qmp node hd).comp (flatSwapCLE_qmp _ _))
        hqS (pivotChart_prod_ae_injOn ⟨pivot, hp⟩)
      have hβ := comp_ae_injOn
        (((pivotChart_prod_qmp ⟨pivot, hp⟩).comp (qNodeOf_qmp node hd)).comp
          (flatSwapCLE_qmp _ _))
        hPqS (ae_injOn_of_injective (qNodeOf M node hd).symm.injective)
      exact hβ
    · simp only [geoChartMapNorm, dif_pos hd, dif_neg hp]
      exact ae_injOn_of_injective Function.injective_id
  · simp only [geoChartMapNorm, dif_neg hd]
    exact ae_injOn_of_injective Function.injective_id

/-! ## The fold: every `geoAtlas` leaf `chartMap` is injective off a null set

Mirroring `GeoLeafLedger.tGeo_leaf_update`: a mutual induction over `tGeo`/`fannedEdges` threading the
invariant "`acc` is QMP and injective off a null set". At a leaf `chartMap = acc` (the invariant IS the
conclusion); at a fanned edge `acc` becomes `acc ∘ geoChartMapNorm _`, and the invariant is maintained
by `comp_ae_injOn` (injectivity) and `QuasiMeasurePreserving.comp` (QMP); chartless edges keep
`acc`. -/

mutual
/-- Every `tGeo acc t` leaf `chartMap` is injective off a null set, given `acc` QMP + injective off
a null set. -/
theorem tGeo_ae_injOn (acc : Params M → Params M)
    (haccQMP : Measure.QuasiMeasurePreserving acc (volume : Measure (Params M)) volume)
    (haccInj : ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn acc (Set.univ \ N)) :
    ∀ t : ResolutionTree M, ∀ c ∈ ResolutionTree.leaves (tGeo acc t),
      ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (Set.univ \ N)
  | .leaf l => by
      intro c hc
      rw [tGeo, ResolutionTree.leaves, List.mem_singleton] at hc
      subst hc
      exact haccInj
  | .branch n edges => by
      intro c hc
      rw [tGeo, ResolutionTree.leaves] at hc
      exact fannedEdges_ae_injOn acc haccQMP haccInj n 0 edges c hc
/-- Companion of `tGeo_ae_injOn` over an edge list. -/
theorem fannedEdges_ae_injOn (acc : Params M → Params M)
    (haccQMP : Measure.QuasiMeasurePreserving acc (volume : Measure (Params M)) volume)
    (haccInj : ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn acc (Set.univ \ N))
    (n : StepData M) (offset : ℕ) :
    ∀ edges : List (Edge M),
      ∀ c ∈ ResolutionTree.edgesLeaves (fannedEdges acc n offset edges),
        ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (Set.univ \ N)
  | [] => by intro c hc; rw [fannedEdges] at hc; cases hc
  | .mk ec esub ch :: rest => by
      intro c hc
      rw [fannedEdges, edgesLeaves_append, List.mem_append] at hc
      rcases hc with hc | hc
      · by_cases hz : dCenterOfEdge n (Edge.mk ec esub ch) = 0
        · rw [if_pos hz] at hc
          simp only [ResolutionTree.edgesLeaves, List.append_nil] at hc
          exact tGeo_ae_injOn acc haccQMP haccInj ch c hc
        · rw [if_neg hz, edgesLeaves_mapMk, List.mem_flatMap] at hc
          obtain ⟨p, _, hcp⟩ := hc
          refine tGeo_ae_injOn
            (acc ∘ geoChartMapNorm (fun _ => id)
              ⟨n, Edge.mk ec esub ch, offset + (p : ℕ)⟩) ?_ ?_ ch c hcp
          · exact haccQMP.comp (geoChartMapNorm_id_qmp _)
          · exact comp_ae_injOn (geoChartMapNorm_id_qmp _)
              (geoChartMapNorm_id_ae_injOn _) haccInj
      · exact fannedEdges_ae_injOn acc haccQMP haccInj n
          (offset + dCenterOfEdge n (Edge.mk ec esub ch)) rest c hc
end

/-- **Every `geoAtlas t` piece's `chartMap` is injective off a null set** (the `acc = id`
specialization of `tGeo_ae_injOn`). -/
theorem geoAtlas_ae_injOn (t : ResolutionTree M) (c : LeafData M) (hc : c ∈ geoAtlas t) :
    ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (Set.univ \ N) := by
  rw [geoAtlas] at hc
  exact tGeo_ae_injOn id (Measure.QuasiMeasurePreserving.id volume)
    (ae_injOn_of_injective Function.injective_id) t c hc

/-- **The `ChartBridge` a.e.-injectivity clause for every built-tree `geoAtlas` piece**: injective
off a null set on the source box (restrict the `univ \ N` form to `srcBox \ N`). This discharges the
first of the three geometric `(B)` clauses of `chartBridgeFaithful_buildTree`. -/
theorem geoAtlas_leaf_ae_injOn (c : LeafData M)
    (hc : c ∈ geoAtlas (buildTree M (conOracle M) (conRoot : ConState L))) :
    ∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn c.chartMap (c.srcBox \ N) := by
  obtain ⟨N, hN0, hNInj⟩ := geoAtlas_ae_injOn _ c hc
  exact ⟨N, hN0, hNInj.mono (Set.diff_subset_diff_left (Set.subset_univ c.srcBox))⟩

end DLNFibre.DLN.RLCT.Engine
