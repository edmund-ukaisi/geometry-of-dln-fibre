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

end DLNFibre.DLN.RLCT.Engine
