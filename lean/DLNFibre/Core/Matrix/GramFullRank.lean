import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# `Core.Matrix.GramFullRank` — Gram determinant from a nonzero square minor

A network-free engine brick. For a tall real matrix `P : Matrix (Fin m) (Fin r) ℝ` with a nonzero
`r×r` minor (some `r`-row selection has invertible determinant), the Gram determinant `det(Pᵀ·P)`
is nonzero — `P` has full column rank `r`, so `Pᵀ·P` (an `r×r` matrix) also has rank `r`, hence
invertible.

The chain: a nonzero `r×r` minor forces `rank P ≥ r`; `rank P ≤ r` (width) gives `rank P = r`;
`Matrix.rank_transpose_mul_self` transports to `rank (PᵀP) = r`; a square matrix of full rank has
nonzero determinant (`Matrix.rank_of_isUnit` contrapositive). The small `det ⟺ rank` bridges are
reproduced locally (they duplicate `Core.RankLocusClosed`'s but avoid importing the quiver stack).

* `det_ne_zero_of_rank_eq` — a square `Fin p` matrix of rank `p` has `det ≠ 0`.
* `gram_det_ne_zero_of_submatrix_det_ne` — `det(PᵀP) ≠ 0` from a nonzero `r×r` minor of `P`.
-/

open Matrix
open scoped BigOperators Matrix

namespace DLNFibre.Core.Matrix

variable {k : Type*} [Field k]

/-- A square matrix whose rank is below its size has zero determinant (`rank_of_isUnit`
contrapositive). Local copy of `Core.RankLocusClosed.det_eq_zero_of_rank_lt` (Mathlib-only). -/
theorem det_eq_zero_of_rank_lt {p : ℕ} (A : Matrix (Fin p) (Fin p) k) (h : A.rank < p) :
    A.det = 0 := by
  by_contra hdet
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit hdet)
  have := Matrix.rank_of_isUnit A hu
  simp only [Fintype.card_fin] at this
  omega

/-- A `Fin a × Fin b` submatrix has rank at most the rank of the full matrix. Local copy of
`Core.RankLocusClosed.rank_submatrix_le_rank`. -/
theorem rank_submatrix_le_rank {p q : ℕ} (A : Matrix (Fin p) (Fin q) k) {a b : ℕ}
    (f : Fin a → Fin p) (g : Fin b → Fin q) :
    (A.submatrix f g).rank ≤ A.rank := by
  have hc := Matrix.cRank_submatrix_le A f g
  rw [← Matrix.cRank_toNat_eq_rank (A.submatrix f g), ← Matrix.cRank_toNat_eq_rank A]
  exact Cardinal.toNat_le_toNat hc ((A.cRank_le_card_width).trans_lt Cardinal.natCast_lt_aleph0)

/-- **A square matrix of full rank is a unit.** `rank A = card` makes the columns linearly
independent (`rank = finrank col-span = #cols`), hence `A` is a unit. -/
theorem isUnit_of_rank_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) k) (h : A.rank = p) :
    IsUnit A := by
  classical
  refine Matrix.linearIndependent_cols_iff_isUnit.mp ?_
  refine (linearIndependent_iff_card_eq_finrank_span (b := A.col)).2 ?_
  -- `#cols = p` and `finrank (span cols) = rank A = p`
  rw [Fintype.card_fin, Set.finrank, ← Matrix.rank_eq_finrank_span_cols, h]

/-- **A square matrix of full rank has nonzero determinant.** From `isUnit_of_rank_eq`. -/
theorem det_ne_zero_of_rank_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) k) (h : A.rank = p) :
    A.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det A).mp (isUnit_of_rank_eq A h)).ne_zero

/-- **A nonzero `r×r` minor forces full column rank.** If some `r`-row / `r`-column selection of a
tall matrix `P : Fin m × Fin r` has nonzero determinant, then `rank P = r` (`≥ r` from the minor,
`≤ r` from the width). -/
theorem rank_eq_of_submatrix_det_ne {m r : ℕ} (P : Matrix (Fin m) (Fin r) k)
    (er : Fin r → Fin m) (ec : Fin r → Fin r) (hdet : (P.submatrix er ec).det ≠ 0) :
    P.rank = r := by
  refine le_antisymm (by simpa using P.rank_le_width) ?_
  -- `rank ≥ r`: if `rank < r` then the selected `r×r` minor has `rank ≤ rank P < r`, so `det = 0`
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hsubrank : (P.submatrix er ec).rank ≤ P.rank := rank_submatrix_le_rank P er ec
  exact hdet (det_eq_zero_of_rank_lt _ (by omega))

/-- **The Gram determinant from a nonzero square minor.** For a tall real matrix `P` with a nonzero
`r×r` minor, `det(Pᵀ·P) ≠ 0`: `rank P = r`, `rank (PᵀP) = rank P = r`
(`Matrix.rank_transpose_mul_self`), and a square matrix of full rank has nonzero determinant. -/
theorem gram_det_ne_zero_of_submatrix_det_ne {m r : ℕ} (P : Matrix (Fin m) (Fin r) ℝ)
    (er : Fin r → Fin m) (ec : Fin r → Fin r) (hdet : (P.submatrix er ec).det ≠ 0) :
    (P.transpose * P).det ≠ 0 := by
  refine det_ne_zero_of_rank_eq _ ?_
  rw [Matrix.rank_transpose_mul_self]
  exact rank_eq_of_submatrix_det_ne P er ec hdet

/-- **The right factor of a full-rank product is a unit.** If `P = U · W` with `P : Fin m × Fin r`
of full column rank `r` and `W : Fin r × Fin r` square, then `det W ≠ 0`: `r = rank P ≤ rank W ≤ r`
(`rank_mul_le_right` + width), so `rank W = r`. -/
theorem right_factor_det_ne_of_rank_eq {m r : ℕ} (P : Matrix (Fin m) (Fin r) k)
    (U : Matrix (Fin m) (Fin r) k) (W : Matrix (Fin r) (Fin r) k)
    (hPUW : P = U * W) (hrank : P.rank = r) : W.det ≠ 0 := by
  refine det_ne_zero_of_rank_eq _ (le_antisymm (by simpa using W.rank_le_width) ?_)
  -- `r = rank P = rank (U·W) ≤ rank W`
  have h := Matrix.rank_mul_le_right U W
  rw [← hPUW, hrank] at h
  exact h

end DLNFibre.Core.Matrix
