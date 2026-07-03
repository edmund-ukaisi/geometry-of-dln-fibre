import DLNFibre.DLN.RLCT.Validate.D1ResidualDerivExpose

/-!
# `DLNFibre.DLN.RLCT.Validate.D1ResidualRankIdentity` — `b1 → b2` closed: the residual Jacobian rank

Glues the `b1` derivative-exposing producer (`dln_hchart_residual_c2_deriv`, exposing
`HasFDerivAt (q(0,·)) (residDerivL) t0`) to the network-free `b2` rank identity
(`DLNFibre.Core.residual_finrank_eq`), via the banked `b1 → b2` bridge
(`jacResid_rank_eq_of_hasFDerivAt`), to conclude

    (jacResid (q(0,·)) t0).rank = (jacFlatL2 H v).rank − m,

where `m = #selected regular directions`. This is the sole remaining CORE-geometry content of the
gate `hrank₂` above the count `(jacFlatL2 H v).rank − m = extraCountRect …` (the `b3` piece).

## The composite match (the `b2` frame)

`euclidReadout (residDerivL) = zeroSel er' ∘ Tresid ∘ f'.symm ∘ sliceMapLin` as linear maps, where:
  * `Tresid z i := (loss-entry gradient of the `i`-th entry) z` — the UN-zeroed flat residual-poly
    Jacobian, in the `entryIdx` frame; `finrank (range Tresid) = jacFlatL2.rank` (row-reindex).
  * `er' := entryIdx ∘ er` — the `b2` output-row selectors; `∃ j, er' j = i ↔ selRow er (decode i)`.
  * `P = f' = chartFDerivEquiv`, so `P.symm = f'.symm`; `hP` from `dChartΦcoord_sel`
    (`f' x (ec j) = Tresid x (er' j)`); `hsurj` from the invertible `(er, ec)` minor.
  * `inj = sliceMapLin`, `range = W = {z : z (ec j) = 0}` (`range_sliceMapLin`).

Then `b2` gives `finrank (range …) = finrank (range Tresid) − m` and the bridge ties the LHS to the
matrix rank. Scope L = 2.
-/

open Matrix Module MeasureTheory Set Filter LinearMap
open scoped ENNReal Topology

namespace DLNFibre.DLN.RLCT

variable {H : Fin (2 + 1) → ℕ} {m : ℕ} {ec : Fin m → Fin (flatDim H)}
  {B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ} {v : Params H} {r : ℕ}
  {er : Fin m → Fin (H 0) × Fin (H 2)}

/-- The `b2` output-row selectors `er' := entryIdx ∘ er : Fin m → Fin (H0*H2)`. -/
noncomputable def erIdx (H : Fin (2 + 1) → ℕ) (er : Fin m → Fin (H 0) × Fin (H 2)) :
    Fin m → Fin (H 0 * H 2) :=
  fun k => entryIdx H (er k)

theorem erIdx_injective (her : Function.Injective er) :
    Function.Injective (erIdx H er) := by
  intro a b hab
  exact her ((entryIdx H).injective hab)

/-- `∃ j, erIdx j = i ↔ selRow er (decode i)` — the `zeroSel`/`selRow` predicate match. -/
theorem exists_erIdx_iff_selRow (i : Fin (H 0 * H 2)) :
    (∃ j, erIdx H er j = i) ↔ selRow er ((entryIdx H).symm i) := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, by rw [erIdx, Equiv.symm_apply_apply]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [erIdx, hk, Equiv.apply_symm_apply]⟩

/-- **The un-zeroed flat residual-polynomial Jacobian at the origin, in the `entryIdx` frame.** The
`i`-th component functional is the loss-entry gradient of the `decode i` entry. -/
noncomputable def Tresid (H : Fin (2 + 1) → ℕ) (v : Params H) :
    (Fin (flatDim H) → ℝ) →ₗ[ℝ] (Fin (H 0 * H 2) → ℝ) :=
  LinearMap.pi fun i =>
    (prodAuxEntryDeriv H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 2
      (Nat.lt_succ_self 2) ((entryIdx H).symm i).1 ((entryIdx H).symm i).2 :
      (Fin (flatDim H) → ℝ) →ₗ[ℝ] ℝ)

@[simp] theorem Tresid_apply (z : Fin (flatDim H) → ℝ) (i : Fin (H 0 * H 2)) :
    Tresid H v z i = prodAuxEntryDeriv H (gmapAt H v) 0 (fun s a b => gmapDeriv H s a b) 2
      (Nat.lt_succ_self 2) ((entryIdx H).symm i).1 ((entryIdx H).symm i).2 z := rfl

/-- `dResidPolyZero` read coordinatewise: the `i`-th coordinate of `dResidPolyZero y` is `0` on a
selected loss entry, the loss-entry gradient of `Tresid` otherwise. -/
theorem dResidPolyZero_apply_coord (y : Fin (flatDim H) → ℝ) (i : Fin (H 0 * H 2)) :
    (dResidPolyZero B v er y) i
      = if selRow er ((entryIdx H).symm i) then 0 else Tresid H v y i := by
  show (dResidPiZero B v er y) i = _
  rw [dResidPiZero, ContinuousLinearMap.pi_apply, dResidPiZeroCoord]
  by_cases hsr : selRow er ((entryIdx H).symm i)
  · simp only [if_pos hsr]; rfl
  · simp only [if_neg hsr]; rw [Tresid_apply]

/-- **The composite match** — `euclidReadout (residDerivL) = zeroSel er' ∘ Tresid ∘ f'.symm ∘
sliceMapLin` (as linear maps), the exact `b2` frame. -/
theorem euclidReadout_residDerivL_eq (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    euclidReadout (residDerivL (B := B) (v := v) (er := er) (ec := ec) hec hminor)
      = (DLNFibre.Core.zeroSel (erIdx H er)).comp
          ((Tresid H v).comp
            ((((chartFDerivEquiv H B v er ec hec hminor :
                  (Fin (flatDim H) → ℝ) ≃ₗ[ℝ] (Fin (flatDim H) → ℝ)).symm) :
                (Fin (flatDim H) → ℝ) →ₗ[ℝ] (Fin (flatDim H) → ℝ)).comp (sliceMapLin hec))) := by
  refine LinearMap.ext fun x => ?_
  funext i
  rw [euclidReadout_apply]
  -- LHS: `residDerivL x i = (dResidPolyZero (f'.symm (sliceMapLin x))) i`.
  show (dResidPolyZero B v er
      ((chartFDerivEquiv H B v er ec hec hminor).symm (sliceMapCLM hec x))) i = _
  rw [dResidPolyZero_apply_coord, sliceMapCLM_apply]
  -- RHS: `zeroSel er' (Tresid (f'.symm (sliceMapLin x))) i`.
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    DLNFibre.Core.zeroSel_apply]
  by_cases hsr : selRow er ((entryIdx H).symm i)
  · rw [if_pos hsr, if_pos ((exists_erIdx_iff_selRow i).mpr hsr)]
  · rw [if_neg hsr, if_neg (fun h => hsr ((exists_erIdx_iff_selRow i).mp h))]; rfl

/-! ## The `b2` hypotheses `hP`, `hinjW`, `hsurj` for the residual composite -/

/-- **`hP` — the selected-coordinate relation.** The chart derivative's selected coordinate `ec j`
reads the `j`-th selected loss-entry gradient, which is the `erIdx j`-row of `Tresid`:
`f' x (ec j) = Tresid x (erIdx j)`. -/
theorem chartFDerivEquiv_sel_eq_Tresid (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0)
    (x : Fin (flatDim H) → ℝ) (j : Fin m) :
    (chartFDerivEquiv H B v er ec hec hminor) x (ec j) = Tresid H v x (erIdx H er j) := by
  -- LHS: `f' x (ec j) = dChartΦ x (ec j) = dChartΦcoord (ec j) x = (er j)-gradient x`.
  have hf' : (chartFDerivEquiv H B v er ec hec hminor) x
      = (dChartΦ H B v er ec) x := by
    rw [← chartFDerivEquiv_coe hec hminor]; rfl
  rw [hf']
  simp only [dChartΦ, ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply]
  rw [dChartΦcoord_sel hec j, Tresid_apply]
  -- RHS: `decode (erIdx j) = er j`, so the two gradients agree.
  rw [erIdx, Equiv.symm_apply_apply]

/-- **`hsurj` — the selected functionals are surjective onto `Fin m → ℝ`.** The composite
`S := selRowProj (erIdx) ∘ Tresid` has matrix `M j c = jacFlatL2 (er j) c`; its `ec`-column subminor
is the invertible `(er, ec)` minor, so `M.rank = m` (full row rank), hence `S` surjective. -/
theorem surjective_selRowProj_comp_Tresid (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    Function.Surjective
      ((DLNFibre.Core.selRowProj (erIdx H er)).comp (Tresid H v)) := by
  classical
  set S : (Fin (flatDim H) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    (DLNFibre.Core.selRowProj (erIdx H er)).comp (Tresid H v) with hSdef
  set M : Matrix (Fin m) (Fin (flatDim H)) ℝ := LinearMap.toMatrix' S with hMdef
  have hMentry : ∀ j c, M j c = jacFlatL2 H v (er j) c := by
    intro j c
    rw [hMdef, LinearMap.toMatrix'_apply, hSdef, LinearMap.comp_apply,
      DLNFibre.Core.selRowProj_apply, Tresid_apply, erIdx, Equiv.symm_apply_apply,
      jacFlatL2_apply_eq_lossEntryDeriv H v (er j).1 (er j).2 c]
  -- `M.submatrix id ec = jacFlatL2.submatrix er ec` (the invertible minor).
  have hsub : M.submatrix (_root_.id : Fin m → Fin m) ec = (jacFlatL2 H v).submatrix er ec := by
    ext j k; rw [Matrix.submatrix_apply, hMentry, Matrix.submatrix_apply]; rfl
  -- rank of the invertible minor is `m`.
  have hminorRank : ((jacFlatL2 H v).submatrix er ec).rank = m := by
    have hunit : IsUnit ((jacFlatL2 H v).submatrix er ec) := by
      rw [Matrix.isUnit_iff_isUnit_det]; exact Ne.isUnit hminor
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  -- column-subset rank ≤ full rank, via the transpose (row-subset of `Mᵀ`).
  have hle : (M.submatrix (_root_.id : Fin m → Fin m) ec).rank ≤ M.rank := by
    rw [← Matrix.rank_transpose (M.submatrix (_root_.id : Fin m → Fin m) ec),
      Matrix.transpose_submatrix, ← Matrix.rank_transpose M]
    exact Matrix.rank_submatrix_le ec (Equiv.refl _) Mᵀ
  have hMrank_ge : m ≤ M.rank := by
    calc m = ((jacFlatL2 H v).submatrix er ec).rank := hminorRank.symm
      _ = (M.submatrix (_root_.id : Fin m → Fin m) ec).rank := by rw [hsub]
      _ ≤ M.rank := hle
  have hMrank_le : M.rank ≤ m := Matrix.rank_le_height M
  have hMrank : M.rank = m := le_antisymm hMrank_le hMrank_ge
  -- full row rank ⟹ `range (toLin' M) = ⊤` ⟹ surjective; transport to `S`.
  have hStoLin : S = Matrix.toLin' M := by rw [hMdef, Matrix.toLin'_toMatrix']
  rw [hStoLin, ← LinearMap.range_eq_top]
  have hrank_fr : Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) = m := by
    have := Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun ℝ (Fin m))
      (Pi.basisFun ℝ (Fin (flatDim H)))
    rw [Matrix.toLin_eq_toLin'] at this
    rw [← this, hMrank]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hrank_fr, Module.finrank_pi, Fintype.card_fin]

/-- **`finrank (range Tresid) = (jacFlatL2 H v).rank`.** `Tresid`'s matrix is `jacFlatL2` with rows
reindexed by the `entryIdx` bijection; rank is reindex-invariant. -/
theorem finrank_range_Tresid_eq :
    Module.finrank ℝ (LinearMap.range (Tresid H v)) = (jacFlatL2 H v).rank := by
  classical
  set M : Matrix (Fin (H 0 * H 2)) (Fin (flatDim H)) ℝ := LinearMap.toMatrix' (Tresid H v)
    with hMdef
  have hMentry : ∀ i c, M i c = jacFlatL2 H v ((entryIdx H).symm i) c := by
    intro i c
    rw [hMdef, LinearMap.toMatrix'_apply, Tresid_apply,
      jacFlatL2_apply_eq_lossEntryDeriv H v ((entryIdx H).symm i).1 ((entryIdx H).symm i).2 c]
  -- `M = jacFlatL2.submatrix (entryIdx H).symm id`, so `M.rank = jacFlatL2.rank`.
  have hMeq : M = (jacFlatL2 H v).submatrix (entryIdx H).symm (_root_.id : Fin (flatDim H) → _) :=
      by
    ext i c; rw [hMentry, Matrix.submatrix_apply]; rfl
  have hMrank : M.rank = (jacFlatL2 H v).rank := by
    rw [hMeq]
    exact Matrix.rank_submatrix (jacFlatL2 H v) (entryIdx H).symm (Equiv.refl _)
  -- `finrank (range Tresid) = M.rank` (both bases `Pi.basisFun`).
  have hrangefr : Module.finrank ℝ (LinearMap.range (Tresid H v)) = M.rank := by
    rw [hMdef, Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun ℝ (Fin (H 0 * H 2)))
      (Pi.basisFun ℝ (Fin (flatDim H))), Matrix.toLin_eq_toLin', Matrix.toLin'_toMatrix']
  rw [hrangefr, hMrank]

/-! ## The assembled `b1 → b2` residual-Jacobian rank identity -/

/-- **`finrank (range residDerivL) = (jacFlatL2 H v).rank − m`.** The `b2` rank identity applied
to the residual composite (composite match ▸ `residual_finrank_eq` ▸ `finrank_range_Tresid_eq`). -/
theorem finrank_range_residDerivL (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    Module.finrank ℝ
      (LinearMap.range (residDerivL (B := B) (v := v) (er := er) (ec := ec) hec hminor :
        (Fin (flatDim H - m) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (H 0 * H 2))))
      = (jacFlatL2 H v).rank - m := by
  -- pass to the pi-readout (finrank-preserving), then to the `b2` composite.
  rw [← finrank_range_euclidReadout
    (residDerivL (B := B) (v := v) (er := er) (ec := ec) hec hminor),
    euclidReadout_residDerivL_eq hec hminor]
  rw [DLNFibre.Core.residual_finrank_eq (Tresid H v) (erIdx H er) ec
    (chartFDerivEquiv H B v er ec hec hminor) (sliceMapLin hec)
    (fun x j => chartFDerivEquiv_sel_eq_Tresid hec hminor x j)
    (range_sliceMapLin hec)
    (surjective_selRowProj_comp_Tresid hec hminor)]
  rw [finrank_range_Tresid_eq]

/-- **The `b1 → b2` residual-Jacobian rank identity.** At an optimal `v` with the invertible
flat-Jacobian minor `(er, ec)`, the first-peel slice residual `q (0, ·)` (from the `b1` producer)
has residual-Jacobian rank exactly `(jacFlatL2 H v).rank − m`:

    ∃ q t0, (C² + slice-vanishing + RLCT) ∧ (jacResid (q(0,·)) t0).rank = (jacFlatL2 H v).rank − m.

Closes the CORE-geometry content of the gate `hrank₂` above the count `(jacFlatL2 H v).rank − m =
extraCountRect …` (the separate `b3` middle-stratum piece). -/
theorem residJacobian_rank_eq (hopt : prod H v = B) (hr : B.rank = r)
    (her : Function.Injective er) (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    ∃ (q : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) → EuclideanSpace ℝ (Fin (H 0 * H 2)))
      (t0 : Fin (flatDim H - m) → ℝ),
      ContDiff ℝ 2 q ∧
      q ((0 : Fin m → ℝ), t0) = 0 ∧
      rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) =>
            (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin m → ℝ), t0) ∧
      (jacResid (fun t : Fin (flatDim H - m) → ℝ => q ((0 : Fin m → ℝ), t)) t0).rank
        = (jacFlatL2 H v).rank - m := by
  obtain ⟨q, t0, hqCD, hq0, hchart, hFD⟩ :=
    dln_hchart_residual_c2_deriv (m := m) (ec := ec) hopt hr her hec hminor
  refine ⟨q, t0, hqCD, hq0, hchart, ?_⟩
  rw [jacResid_rank_eq_of_hasFDerivAt
      (fun t : Fin (flatDim H - m) → ℝ => q ((0 : Fin m → ℝ), t))
      (residDerivL (B := B) (v := v) (er := er) (ec := ec) hec hminor) t0 hFD]
  exact finrank_range_residDerivL hec hminor

end DLNFibre.DLN.RLCT
