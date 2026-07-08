import DLNFibre.DLN.RLCT.Validate.D1L2PhiExpl

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeBlockModel` — the general-`L` block-decomposition coordinate model

The general-`L` analogue of the L = 2 block model (`BlockParamsL2` / `blockFlatEquiv_L2`,
`D1L2PhiExpl`), the FOUNDATION the general-`L` explicit-Schur chart is built on. Because `Params H` is
DEFINITIONALLY the layer `Pi` type `∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`, the
layer split is free and the whole model is one `LinearEquiv.piCongrRight` of per-layer
`Matrix.reindexLinearEquiv`s, precomposed with the (linear) flatten-inverse `paramsEquivFlatLinear`.

The common pivot is a family `ι : (s : Fin (L+1)) → Fin r → Fin (H s)` of injections — one per VERTEX
(the L = 2 model's `I, K, J`); layer `s : Fin L` reindexes its rows by `ι s.castSucc`, its columns by
`ι s.succ`, so the pivot `r × r` corner (`toBlocks₁₁`) of the block form is exactly the layer's minor
at those pivot indices (`blockFlatEquivGen_toBlocks₁₁`). This is what the Schur reparametrisation
reads: the invertible pivot at each vertex, established downstream from a common-pivot existence lemma
(the general-`L` analogue of `exists_common_pivot_L2_at`).

Pure linear algebra; no chart `Φ`, no IFT, no measure theory. Continuous by
`LinearEquiv.toContinuousLinearEquiv` (finite-dimensional).
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-`L` block-decomposed parameter type** at a rank-`r` per-vertex pivot: each layer
matrix reindexed so the `r` pivot rows/columns sit in the top-left `Fin r ⊕ Fin (H_s − r)` block. The
`Params`-analogue of `BlockParamsL2`, as the layer `Pi`. -/
abbrev BlockParamsGen (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  ∀ s : Fin L,
    Matrix (Fin r ⊕ Fin (H s.castSucc - r)) (Fin r ⊕ Fin (H s.succ - r)) ℝ

/-- **The per-layer pivot reindex** `Params H ≃ₗ[ℝ] BlockParamsGen H r ι`: layer `s` reindexed by the
pivot injections at its two vertices `s.castSucc`, `s.succ` (`sumSplit`), assembled over layers by
`LinearEquiv.piCongrRight`. -/
noncomputable def paramsBlockEquivGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)) :
    Params H ≃ₗ[ℝ] BlockParamsGen H r :=
  LinearEquiv.piCongrRight (fun s : Fin L =>
    Matrix.reindexLinearEquiv ℝ ℝ
      (sumSplit (ι s.castSucc) (hι s.castSucc)).symm
      (sumSplit (ι s.succ) (hι s.succ)).symm)

/-- **`blockFlatEquivGen` — the general-`L` block-reindexing coordinate model.** A CONTINUOUS
ℝ-linear equiv `(Fin (flatDim H) → ℝ) ≃L[ℝ] BlockParamsGen H r`: the (linear) flatten-inverse
`≫` the per-layer pivot reindex. The general-`L` analogue of `blockFlatEquiv_L2`. -/
noncomputable def blockFlatEquivGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)) :
    (Fin (flatDim H) → ℝ) ≃L[ℝ] BlockParamsGen H r :=
  ((paramsEquivFlatLinear H).symm.trans (paramsBlockEquivGen H r ι hι)).toContinuousLinearEquiv

/-- Layer `s` of `blockFlatEquivGen x` is the pivot-reindexed layer `s` of the (linear)
flatten-inverse of `x`. -/
theorem blockFlatEquivGen_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (x : Fin (flatDim H) → ℝ) (s : Fin L) :
    blockFlatEquivGen H r ι hι x s
      = Matrix.reindex (sumSplit (ι s.castSucc) (hι s.castSucc)).symm
          (sumSplit (ι s.succ) (hι s.succ)).symm ((paramsEquivFlatLinear H).symm x s) := by
  rw [blockFlatEquivGen, LinearEquiv.coe_toContinuousLinearEquiv']
  rfl

/-- **The pivot `r × r` block is the pivot minor.** The `toBlocks₁₁` corner of layer `s` of
`blockFlatEquivGen x` is exactly that layer's minor at the pivot rows `ι s.castSucc`, columns
`ι s.succ` — the invertible pivot the Schur reparametrisation consumes. General-`L` analogue of
`blockFlatEquiv_L2_toBlocks₁₁_fst`. -/
theorem blockFlatEquivGen_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (x : Fin (flatDim H) → ℝ) (s : Fin L) :
    (blockFlatEquivGen H r ι hι x s).toBlocks₁₁
      = ((paramsEquivFlatLinear H).symm x s).submatrix (ι s.castSucc) (ι s.succ) := by
  rw [blockFlatEquivGen_apply]
  ext a b
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, sumSplit_inl]

end DLNFibre.DLN.RLCT
