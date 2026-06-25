import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestEFullSregComparability` — the L2-PIN2 producer atoms

The eventual-neighborhood atoms feeding `hproducer` (the last L2 body piece of
`framedParams_split_eq_frame_raw` in `DeepestGaugeConstruction`). Design cert:
`expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/hproducer-decomp-cert.md`.

This module imports `DeepestGaugeConstruction` (where `deepestEFull`, `framedParamsPivot`, and the
producer live) so it can reference those objects. The producer's body is wired in
`DeepestGaugeConstruction` itself (single proof); the reusable eventual-neighborhood atoms that do
NOT belong inside that one proof live here, named and independently auditable.

## Landed this module

- `eventually_isUnit_of_continuous_eq_one` — the **S5a invertibility germ** (network-free): a
  continuous matrix-valued map equal to `1` at the basepoint is invertible on a neighborhood. `det`
  continuous, `det 1 = 1 ≠ 0`, `ContinuousAt.eventually_ne`, `Matrix.isUnit_iff_isUnit_det`. The
  abstract core of the producer's `det P00 ≠ 0` open set (instantiated with the `(1,1)`-block map).
-/

open Matrix Filter Topology
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **S5a invertibility germ** (network-free). A continuous matrix-valued map `M : X → Matrix r r ℝ`
equal to the identity at a basepoint `x0` is invertible (`IsUnit`) on a neighborhood of `x0`. The
determinant `x ↦ (M x).det` is continuous (`Continuous.matrix_det`), `= (1).det = 1 ≠ 0` at `x0`,
so by `ContinuousAt.eventually_ne` the determinant is eventually nonzero, hence `M x` is a unit
(`Matrix.isUnit_iff_isUnit_det`). The abstract core of the producer's `det P00 ≠ 0` open set. -/
theorem eventually_isUnit_of_continuous_eq_one {X r : Type*} [TopologicalSpace X]
    [Fintype r] [DecidableEq r] {M : X → Matrix r r ℝ} (hM : Continuous M) {x0 : X}
    (hx0 : M x0 = 1) :
    ∀ᶠ x in 𝓝 x0, IsUnit (M x) := by
  -- `x ↦ (M x).det` is continuous, and `= 1` at `x0`.
  have hdet : Continuous fun x => (M x).det := hM.matrix_det
  have hdet0 : (M x0).det = 1 := by rw [hx0]; simp
  -- The determinant is eventually `≠ 0` near `x0` (it is `1 ≠ 0` there).
  have hne : (M x0).det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hev : ∀ᶠ x in 𝓝 x0, (M x).det ≠ 0 :=
    (hdet.continuousAt).eventually_ne hne
  -- A matrix is a unit iff its determinant is a unit; over ℝ, `det ≠ 0 ↔ IsUnit det`.
  refine hev.mono (fun x hx => ?_)
  rw [Matrix.isUnit_iff_isUnit_det]
  exact Ne.isUnit hx

/-- The layer partial-product matrix is continuous in the parameters (local helper; mirrors the
private `continuous_prodAux` in `DeepestGaugeChart`, not exported — and the `LossContinuity` public
copy is unimportable here, a same-namespace `continuous_dlnLoss` collision). Induction on chain
length: base `prodAux 0 = 1` constant; step `prodAux (k+1) = prodAux k * layer k`. -/
private theorem continuous_prodAux' (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
    Continuous (fun A : Params H => prodAux H A k hk) := by
  revert hk
  induction k with
  | zero =>
      intro hk
      simpa [prodAux] using
        (continuous_const :
          Continuous (fun _ : Params H => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)))
  | succ k ih =>
      intro hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      let layer : Params H → Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ :=
        fun A => ((by rw [e1, e2]; exact A ⟨k, hkL⟩) :
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
      have hLayer : Continuous layer := by
        dsimp [layer]
        simpa only [e1, e2, eq_mpr_eq_cast, cast_eq] using
          (continuous_apply (⟨k, hkL⟩ : Fin L) :
            Continuous (fun A : Params H => A ⟨k, hkL⟩))
      have hMul : Continuous (fun A : Params H => prodAux H A k hk' * layer A) :=
        (ih hk').matrix_mul hLayer
      exact hMul.congr fun A => by dsimp [layer]; rfl

/-- The multiplication map `A ↦ prod H A` is continuous (`continuous_prodAux'` at `k = L`). -/
private theorem continuous_prod' (H : Fin (L + 1) → ℕ) : Continuous (prod H) :=
  continuous_prodAux' H L (Nat.lt_succ_self L)

/-- **The producer's `(1,1)`-block map is continuous in `w`.** `w ↦ P00 w` where
`P00 w = (reindex e₁ e₂ (P0 · (prod ((paramsEquivFlat).symm w) − B) · QL)).toBlocks₁₁ + 1`. The
flattening `(paramsEquivFlat).symm` is a continuous linear equiv (`paramsEquivFlatCLE`), `prod` is
continuous (`continuous_prod`), and the remaining matrix algebra (`− B`, `P0 · · QL`, reindex,
`toBlocks₁₁`, `+ 1`) is entrywise continuous. The continuity input to S5a invertibility. -/
theorem continuous_block₁₁_map (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
    (e₁ : Fin (H 0) ≃ Fin r ⊕ Fin (H 0 - r))
    (e₂ : Fin (H (Fin.last L)) ≃ Fin r ⊕ Fin (H (Fin.last L) - r)) :
    Continuous fun w : Fin (flatDim H) → ℝ =>
      (Matrix.reindex e₁ e₂
          (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁
        + (1 : Matrix (Fin r) (Fin r) ℝ) := by
  -- `w ↦ (paramsEquivFlat).symm w` continuous (the CLE's inverse), so `prod ∘ symm` continuous.
  -- The CLE and the equiv share the SAME forward function (`paramsEquivFlatCLE_coe`), so the SAME
  -- inverse (an equiv's inverse is determined by its forward map).
  have hsymmcoe : ⇑(paramsEquivFlatCLE H).symm = ⇑(paramsEquivFlat H).symm := by
    funext y
    -- Apply the (injective) forward map: `equiv ((CLE).symm y)` and `equiv ((equiv).symm y) = y`
    -- agree, since `equiv` and `CLE` share the forward function (`paramsEquivFlatCLE_coe`).
    apply (paramsEquivFlat H).injective
    rw [(paramsEquivFlat H).apply_symm_apply]
    have hcle : (paramsEquivFlat H) ((paramsEquivFlatCLE H).symm y)
        = (paramsEquivFlatCLE H) ((paramsEquivFlatCLE H).symm y) := by
      rw [← paramsEquivFlatCLE_coe H]
    rw [hcle, ContinuousLinearEquiv.apply_symm_apply]
  have hsymm : Continuous fun w : Fin (flatDim H) → ℝ => (paramsEquivFlat H).symm w := by
    rw [← hsymmcoe]; exact (paramsEquivFlatCLE H).symm.continuous
  have hprod : Continuous fun w : Fin (flatDim H) → ℝ => prod H ((paramsEquivFlat H).symm w) :=
    (continuous_prod' H).comp hsymm
  -- `w ↦ P0 · (prod − B) · QL` continuous, then reindex (relabel) + toBlocks₁₁ (submatrix) + `+1`.
  have hconj : Continuous fun w : Fin (flatDim H) → ℝ =>
      P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL :=
    (continuous_const.matrix_mul ((hprod.sub continuous_const))).matrix_mul continuous_const
  have hreindex : Continuous fun w : Fin (flatDim H) → ℝ =>
      Matrix.reindex e₁ e₂ (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL) :=
    hconj.matrix_reindex e₁ e₂
  -- `toBlocks₁₁ = submatrix Sum.inl Sum.inl` (continuous), then `+ const`.
  exact (hreindex.matrix_submatrix Sum.inl Sum.inl).add continuous_const

/-- **S5a — the producer's pivot block is eventually invertible** (`hproducer` conjunct).
The `(1,1)` block `P00 w = (reindex e₁ e₂ (P0·(prod((symm) w) − B)·QL)).toBlocks₁₁ + 1` is `1` at
the deepest point `w0` (`prod ((symm) w0) = prod (deepestPoint) = B`, so the conjugated residual is
`0`, its reindex is `0`, the `(1,1)` block is `0`, `+ 1 = 1`) — hence invertible on a neighborhood
(`continuous_block₁₁_map` + `eventually_isUnit_of_continuous_eq_one`). The producer's `P00 := this
block`, so `P00 − 1 = (reindex …).toBlocks₁₁` is the actual residual block. -/
theorem eventually_P00_invertible (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
    (e₁ : Fin (H 0) ≃ Fin r ⊕ Fin (H 0 - r))
    (e₂ : Fin (H (Fin.last L)) ≃ Fin r ⊕ Fin (H (Fin.last L) - r)) :
    ∀ᶠ w in 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
      IsUnit ((Matrix.reindex e₁ e₂
          (P0 * (prod H ((paramsEquivFlat H).symm w) - B) * QL)).toBlocks₁₁
        + (1 : Matrix (Fin r) (Fin r) ℝ)) := by
  apply eventually_isUnit_of_continuous_eq_one (continuous_block₁₁_map H r B P0 QL e₁ e₂)
  -- At `w0`: `(paramsEquivFlat).symm w0 = deepestPoint`, `prod deepestPoint = B`, residual `= 0`.
  have hsymm0 : (paramsEquivFlat H).symm ((paramsEquivFlat H) (deepestPoint H r B hB hr hL))
      = deepestPoint H r B hB hr hL := (paramsEquivFlat H).symm_apply_apply _
  have hprod0 : prod H (deepestPoint H r B hB hr hL) = B :=
    (deepestPoint_isDeep H r B hB hr hL).1
  rw [hsymm0, hprod0]
  -- `P0 · (B − B) · QL = 0`, its reindex is `0`, `toBlocks₁₁ 0 = 0`, `0 + 1 = 1`.
  have hz : P0 * (B - B) * QL = 0 := by rw [sub_self, Matrix.mul_zero, Matrix.zero_mul]
  rw [hz]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply,
    Matrix.zero_apply, Matrix.add_apply, zero_add]

end DLNFibre.DLN.RLCT
