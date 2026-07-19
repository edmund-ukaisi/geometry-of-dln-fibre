import DLNFibre.DLN.RLCT.Engine.GeoDiagSwap
import DLNFibre.DLN.RLCT.Engine.DivBirthReach

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoFoldRegroup` — the fold-Jacobian regrouping cocycle machinery (t14)

The internal machinery for `geoAtlas_fold_det` (`GeoLeafJacobian`). Following the t11 handoff addendum
(§HANDOFF) and cert §1/§2 (`threads/18-fold-regroup/cert-fold-regroup.md`):

* **Differentiability** of the normalized chart `geoChartMapNorm (fun _ => id)` (so the parametric
  chain-rule fold `abs_det_fderiv_foldr_comp` applies).
* **(α) the §0 chart-action** of `geoChartMapNorm` on flat coordinates (the workhorse for the regroup).
* **(β) the coherence** `divCoord = diagTargetOf` (the leaf ledger names the same diagonal cell the chart
  reads).
* the **leafPaths → foldr bridge** + the **cocycle maintenance** (threaded ledger, innermost-first).

Built incrementally, banking greens. The headline is scoped to `conRoot` (t14 correction, ruling A).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **`geoChartMapNorm (fun _ => id)` is differentiable everywhere.** On-cone it is the composite
`geoChartMap g ∘ S ∘ id` (`geoChartMap_differentiable` + `flatSwapCLE_differentiable`); off-cone / out of
range it is `id`. So any list of these charts satisfies the `abs_det_fderiv_foldr_comp` hypothesis. -/
theorem geoChartMapNorm_differentiable (g : GeoChart M) :
    Differentiable ℝ (geoChartMapNorm (fun _ => id) g) := by
  unfold geoChartMapNorm
  by_cases hd : dCenterOfNode M g.node ≤ flatDim M
  · rw [dif_pos hd]
    by_cases hp : g.pivot < dCenterOfNode M g.node
    · rw [dif_pos hp]
      exact (geoChartMap_differentiable g).comp
        ((flatSwapCLE_differentiable M _ _).comp differentiable_id)
    · rw [dif_neg hp]; exact differentiable_id
  · rw [dif_neg hd]; exact differentiable_id

/-! ## (α) The §0 chart-action of `geoChartMap`/`geoChartMapNorm` on flat coordinates -/

/-- **The second component of `qOfCenterCLE` reads the complement coordinate** (`_snd`, mirror of the
banked `qOfCenterCLE_fst_apply`): `(q y).2 j = z_{centerPerm.symm (inr j)}(y)`. -/
theorem qOfCenterCLE_snd_apply (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (w : Params M) (j : Fin (flatDim M - d)) :
    (qOfCenterCLE M c hinj w).2 j = paramsEquivFlat M w ((centerPerm M c hinj).symm (Sum.inr j)) := by
  have hcoe : ⇑(LinearEquiv.piCongrLeft ℝ (fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
      (centerPerm M c hinj)) = ⇑(Equiv.piCongrLeft (fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
      (centerPerm M c hinj)) := rfl
  unfold qOfCenterCLE
  simp only [ContinuousLinearEquiv.trans_apply, LinearEquiv.coe_toContinuousLinearEquiv',
    paramsEquivFlatCLE_coe, LinearEquiv.sumArrowLequivProdArrow_apply_snd, hcoe]
  conv_lhs => rw [show (Sum.inr j : Fin d ⊕ Fin (flatDim M - d))
        = centerPerm M c hinj ((centerPerm M c hinj).symm (Sum.inr j)) from
      (Equiv.apply_symm_apply _ _).symm]
  rw [Equiv.piCongrLeft_apply_apply]

/-- **The master flat read** of the `qOfCenterCLE` split: every flat coordinate `cc` is read off the
split by routing through `centerPerm` — center cells (`inl`) from the first factor, spectators (`inr`)
from the second. `z_cc(y) = Sum.elim (q y).1 (q y).2 (centerPerm cc)`. -/
theorem qOfCenterCLE_flat_read (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (y : Params M) (cc : Fin (flatDim M)) :
    paramsEquivFlat M y cc
      = Sum.elim (qOfCenterCLE M c hinj y).1 (qOfCenterCLE M c hinj y).2
          (centerPerm M c hinj cc) := by
  rcases h : centerPerm M c hinj cc with i | j
  · have hcc : cc = c i := by
      rw [← centerPerm_symm_inl M c hinj i, ← h, Equiv.symm_apply_apply]
    rw [Sum.elim_inl, hcc, qOfCenterCLE_fst_apply]
  · have hcc : cc = (centerPerm M c hinj).symm (Sum.inr j) := by
      rw [← h, Equiv.symm_apply_apply]
    rw [Sum.elim_inr, hcc, qOfCenterCLE_snd_apply]

/-- `centerPerm` sends a center cell `c i` to `Sum.inl i` (inverse of `centerPerm_symm_inl`). -/
theorem centerPerm_apply_c (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (i : Fin d) : centerPerm M c hinj (c i) = Sum.inl i := by
  rw [← centerPerm_symm_inl M c hinj i, Equiv.apply_symm_apply]

/-- **`q` conjugates `geoChartMap` to the block map**: on-cone, `q (geoChartMap g x) = (pivotChart ⟨pivot⟩ ×
id) (q x)` — the chart acts as `pivotChart` on the center block and identity on the rest, read through the
`q`-split (`conjBlockMap` + `apply_symm_apply`). -/
theorem q_comp_geoChartMap (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd)
        (geoChartMap (dCenterOfNode M) (qNodeOf M) g x)
      = Prod.map (pivotChart (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) id
          (qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) x) := by
  have hfun : geoChartMap (dCenterOfNode M) (qNodeOf M) g
      = conjBlockMap (qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd))
          (pivotChart (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) := by
    unfold geoChartMap qNodeOf conjBlockMap
    rw [dif_pos hd, dif_pos hp]; rfl
  rw [hfun]
  simp only [conjBlockMap, ContinuousLinearEquiv.apply_symm_apply]

/-- **The master flat action of `geoChartMap`** (on-cone): every flat coordinate `cc` of the image is
read through the `q`-split — center cells go through `pivotChart`, spectators pass through. -/
theorem paramsEquivFlat_geoChartMap (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node)
    (cc : Fin (flatDim M)) :
    paramsEquivFlat M (geoChartMap (dCenterOfNode M) (qNodeOf M) g x) cc
      = Sum.elim (pivotChart (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))
            (qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) x).1)
          (qOfCenterCLE M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) x).2
          (centerPerm M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) cc) := by
  rw [qOfCenterCLE_flat_read M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd)
      (geoChartMap (dCenterOfNode M) (qNodeOf M) g x) cc, q_comp_geoChartMap g x hd hp]
  rfl

/-- **(α)-pivot** (the pivot coordinate is FREE): `z_{c ⟨pivot⟩}(geoChartMap g x) = z_{c ⟨pivot⟩}(x)`. -/
theorem geoChartMap_flat_pivot (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    paramsEquivFlat M (geoChartMap (dCenterOfNode M) (qNodeOf M) g x)
        (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
      = paramsEquivFlat M x (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) := by
  rw [paramsEquivFlat_geoChartMap g x hd hp, centerPerm_apply_c, Sum.elim_inl, pivotChart,
    if_pos rfl, qOfCenterCLE_fst_apply]

/-- **(α)-center** (a non-pivot center cell is SCALED by the pivot): for `i ≠ ⟨pivot⟩`,
`z_{c i}(geoChartMap g x) = z_{c ⟨pivot⟩}(x) · z_{c i}(x)`. -/
theorem geoChartMap_flat_center (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node)
    (i : Fin (dCenterOfNode M g.node)) (hi : i ≠ (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) :
    paramsEquivFlat M (geoChartMap (dCenterOfNode M) (qNodeOf M) g x) (cNodeOf M g.node hd i)
      = paramsEquivFlat M x (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
        * paramsEquivFlat M x (cNodeOf M g.node hd i) := by
  rw [paramsEquivFlat_geoChartMap g x hd hp, centerPerm_apply_c, Sum.elim_inl, pivotChart,
    if_neg hi, qOfCenterCLE_fst_apply, qOfCenterCLE_fst_apply]

/-- **(α)-spectator** (a non-center cell is FIXED): if `cc` is not a center cell (`∀ i, c i ≠ cc`),
`z_cc(geoChartMap g x) = z_cc(x)`. -/
theorem geoChartMap_flat_spectator (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node)
    (cc : Fin (flatDim M)) (hcc : ∀ i, cNodeOf M g.node hd i ≠ cc) :
    paramsEquivFlat M (geoChartMap (dCenterOfNode M) (qNodeOf M) g x) cc
      = paramsEquivFlat M x cc := by
  rw [paramsEquivFlat_geoChartMap g x hd hp]
  rcases h : centerPerm M (cNodeOf M g.node hd) (cNodeOf_injective M g.node hd) cc with i | j
  · exact absurd (by rw [← centerPerm_symm_inl M (cNodeOf M g.node hd)
        (cNodeOf_injective M g.node hd) i, ← h, Equiv.symm_apply_apply] :
        cNodeOf M g.node hd i = cc) (hcc i)
  · rw [Sum.elim_inr, qOfCenterCLE_snd_apply]
    congr 1
    rw [← h, Equiv.symm_apply_apply]

/-- **`geoChartMapNorm (fun _ => id)` on-cone unfolds to `geoChartMap ∘ S`** (the diagonal-normalization
swap composed inside, gauge `= id`). The bridge that lets the `(α)` `geoChartMap` reads + `flatSwapCLE`
relabel compute the normalized chart's flat action. -/
theorem geoChartMapNorm_apply_oncone (g : GeoChart M) (x : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    geoChartMapNorm (fun _ => id) g x
      = geoChartMap (dCenterOfNode M) (qNodeOf M) g
          (flatSwapCLE M (cNodeOf M g.node hd (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
            (diagTargetOf M g.node g.edge (by omega)) x) := by
  unfold geoChartMapNorm
  rw [dif_pos hd, dif_pos hp]
  rfl

end DLNFibre.DLN.RLCT.Engine
