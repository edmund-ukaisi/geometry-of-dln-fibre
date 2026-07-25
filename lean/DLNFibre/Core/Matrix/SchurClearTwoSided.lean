import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `DLNFibre.Core.Matrix.SchurClearTwoSided` — two-sided block elimination at a unit pivot

Two-sided Gaussian elimination of a `2×2` block matrix whose leading block is the **identity**
(the unit pivot). Two unipotent block-shears — `lowerShear C = [[1,0],[C,1]]` (row op) and
`upperShear B = [[1,B],[0,1]]` (col op) — conjugate a block matrix `[[1, B],[C, D]]` to the
block-diagonal Schur form `[[1, 0],[0, D − C·B]]`, and back.

This is the unit-pivot specialisation of the LDU/Schur decomposition
(`Matrix.fromBlocks_eq_of_invertible₁₁`), and is the network-free linear-algebra brick behind the
per-step two-sided hideal of the resolution atlas (the aoyagi-engine general-`d` route). Keeping the
pivot the identity buys three things over the general invertible-pivot form:

* the Schur complement is `D − C·B` (no `A⁻¹` / `⅟A`), so the statements are over a bare `[Ring R]`
  with **no `Invertible`/`IsUnit` plumbing** and no `nonsing_inv`/`invOf` diamond;
* the shears are **unipotent**, so their inverses are the same shears with negated off-blocks
  (polynomial, `lowerShear (-C)`, `upperShear (-B)`) — the invertibility the caller needs is a plain
  ring identity, not a typeclass;
* everything lives over **abstract `Sum` index types** `l ⊕ m` (Mathlib's `fromBlocks` grain), so
  there is no dependent-`Fin`-width cast-tax; the reconciliation to a flat `Fin (r + s)`
  presentation is a single `finSumFinEquiv`-reindex (`schur_clear_two_sided_fin`), transported
  through `Matrix.submatrix_mul_equiv`.

Complements `RankNormalFormTriangular` (which handles the one-sided normalizers at an *invertible*
pivot over `ℝ`/`Fin`); this file is the two-sided, unit-pivot, `Ring`/`Sum` form.

## Main results
- `schur_clear_two_sided` — `lowerShear (-C) · [[1,B],[C,D]] · upperShear (-B) = [[1,0],[0,D−C·B]]`.
- `schur_reconstruct` — the reverse: block-diagonal back to `[[1,B],[C,D]]`.
- `lowerShear_mul` / `upperShear_mul` — the shear composition (group) law.
- `lowerShear_neg_mul` / `upperShear_neg_mul` — the shears are unipotent (mutually inverse).
- `isUnit_lowerShear` / `isUnit_upperShear` — hence units.
- `schur_clear_two_sided_fin` — the same clearing transported to flat `Fin (r + s)` widths.
-/

open Matrix
namespace DLNFibre.Core.Matrix

section Blocks
variable {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]
variable {R : Type*} [Ring R]

/-- The lower unipotent block-shear `[[1,0],[C,1]]` on `l ⊕ m` (a row operation). -/
def lowerShear (C : Matrix m l R) : Matrix (l ⊕ m) (l ⊕ m) R :=
  fromBlocks 1 0 C 1

/-- The upper unipotent block-shear `[[1,B],[0,1]]` on `l ⊕ m` (a column operation). -/
def upperShear (B : Matrix l m R) : Matrix (l ⊕ m) (l ⊕ m) R :=
  fromBlocks 1 B 0 1

/-- Lower shears compose additively: `[[1,0],[C,1]] · [[1,0],[C',1]] = [[1,0],[C+C',1]]`. -/
theorem lowerShear_mul (C C' : Matrix m l R) :
    lowerShear C * lowerShear C' = lowerShear (C + C') := by
  rw [lowerShear, lowerShear, lowerShear, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, by simp, by simp, by simp⟩

/-- Upper shears compose additively: `[[1,B],[0,1]] · [[1,B',][0,1]] = [[1,B+B'],[0,1]]`. -/
theorem upperShear_mul (B B' : Matrix l m R) :
    upperShear B * upperShear B' = upperShear (B + B') := by
  rw [upperShear, upperShear, upperShear, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, ?_, by simp, by simp⟩
  rw [Matrix.one_mul, Matrix.mul_one, add_comm]

omit [Fintype l] [Fintype m] in
/-- `lowerShear 0 = 1`. -/
@[simp] theorem lowerShear_zero : lowerShear (0 : Matrix m l R) = 1 := by
  rw [lowerShear, fromBlocks_one]

omit [Fintype l] [Fintype m] in
/-- `upperShear 0 = 1`. -/
@[simp] theorem upperShear_zero : upperShear (0 : Matrix l m R) = 1 := by
  rw [upperShear, fromBlocks_one]

/-- The lower shears are mutually inverse: `[[1,0],[-C,1]] · [[1,0],[C,1]] = 1`. -/
theorem lowerShear_neg_mul (C : Matrix m l R) : lowerShear (-C) * lowerShear C = 1 := by
  rw [lowerShear_mul, neg_add_cancel, lowerShear_zero]

/-- The upper shears are mutually inverse: `[[1,-B],[0,1]] · [[1,B],[0,1]] = 1`. -/
theorem upperShear_neg_mul (B : Matrix l m R) : upperShear (-B) * upperShear B = 1 := by
  rw [upperShear_mul, neg_add_cancel, upperShear_zero]

/-- The lower shear is a unit; inverse `lowerShear (-C)` (both sides, via `lowerShear_mul`). -/
theorem isUnit_lowerShear (C : Matrix m l R) : IsUnit (lowerShear C) := by
  letI : Invertible (lowerShear C) :=
    ⟨lowerShear (-C), lowerShear_neg_mul C, by rw [lowerShear_mul, add_neg_cancel, lowerShear_zero]⟩
  exact isUnit_of_invertible _

/-- The upper shear is a unit; inverse `upperShear (-B)` (both sides, via `upperShear_mul`). -/
theorem isUnit_upperShear (B : Matrix l m R) : IsUnit (upperShear B) := by
  letI : Invertible (upperShear B) :=
    ⟨upperShear (-B), upperShear_neg_mul B, by rw [upperShear_mul, add_neg_cancel, upperShear_zero]⟩
  exact isUnit_of_invertible _

/-- **Two-sided block elimination at a unit pivot.** The unipotent shears clear the off-diagonal
blocks of `[[1, B],[C, D]]`, leaving the block-diagonal Schur form `[[1, 0],[0, D − C·B]]`. -/
theorem schur_clear_two_sided (B : Matrix l m R) (C : Matrix m l R) (D : Matrix m m R) :
    lowerShear (-C) * fromBlocks (1 : Matrix l l R) B C D * upperShear (-B)
      = fromBlocks 1 0 0 (D - C * B) := by
  rw [lowerShear, upperShear, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, by simp, by simp, ?_⟩
  simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one,
    neg_add_cancel, Matrix.zero_mul]
  abel

/-- **The reverse:** the shears reconstruct `[[1, B],[C, D]]` from the block-diagonal Schur form. -/
theorem schur_reconstruct (B : Matrix l m R) (C : Matrix m l R) (D : Matrix m m R) :
    lowerShear C * fromBlocks (1 : Matrix l l R) 0 0 (D - C * B) * upperShear B
      = fromBlocks 1 B C D := by
  rw [lowerShear, upperShear, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, by simp, by simp, ?_⟩
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
  abel

end Blocks

section Fin
variable {R : Type*} [Ring R] {r s : ℕ}

/-- **The flat-`Fin` reconciliation.** The two-sided clearing, reindexed from the `Sum`-block grain
`Fin r ⊕ Fin s` to a flat `Fin (r + s)` presentation via `finSumFinEquiv`, holds unchanged — the
relabel is a single `submatrix`/`reindex`, with no dependent-`Fin`-width cast-tax. -/
theorem schur_clear_two_sided_fin (B : Matrix (Fin r) (Fin s) R) (C : Matrix (Fin s) (Fin r) R)
    (D : Matrix (Fin s) (Fin s) R) :
    reindex finSumFinEquiv finSumFinEquiv (lowerShear (-C))
        * reindex finSumFinEquiv finSumFinEquiv (fromBlocks (1 : Matrix (Fin r) (Fin r) R) B C D)
        * reindex finSumFinEquiv finSumFinEquiv (upperShear (-B))
      = reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (D - C * B)) := by
  simp only [reindex_apply, Matrix.submatrix_mul_equiv]
  rw [schur_clear_two_sided]

end Fin

/-! ## Non-vacuity

The clearing genuinely acts (not the vacuous already-diagonal case): whenever `C ≠ 0` or `B ≠ 0`,
`lowerShear (-C)` resp. `upperShear (-B)` is `≠ 1`, and the Schur complement `D − C·B` differs from
`D`. The following witness pins the statement at concrete `(r,s) = (1,1)` over `ℚ`. -/

/-- Non-vacuity witness: the two-sided clearing at `(r,s) = (1,1)` over `ℚ`. -/
example (B C D : Matrix (Fin 1) (Fin 1) ℚ) :
    lowerShear (-C) * fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) B C D * upperShear (-B)
      = fromBlocks 1 0 0 (D - C * B) :=
  schur_clear_two_sided B C D

end DLNFibre.Core.Matrix
