import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGramSchur` — Gram Schur-complement determinant recursion

**Thread `genm-catclose`, Cat I good-stratum piece P3 (algebraic half).** Appending one row `w` to
a matrix `A` (whose Gram `A Aᵀ` is invertible) multiplies the Gram determinant by the
*Schur-complement scalar* `‖w‖² − (A·w)ᵀ (A Aᵀ)⁻¹ (A·w)`:

    det( Q Qᵀ ) = det( A Aᵀ ) · ( w⬝w − (A·w) ⬝ ((A Aᵀ)⁻¹ · (A·w)) ),   Q = A with `w` appended.

This is the algebraic core of the row-residual recursion `det(Q_b Q_bᵀ) = ∏ dist(rowᵢ, span prev)²`
(catint cert). The Schur-complement scalar equals `dist(w, rowspan A)² = ‖P_{V⊥} w‖²` (the geometric
identification — a separate brick); this file establishes only the pure-matrix determinant identity,
via Mathlib `det_fromBlocks₁₁`.

S2-FREE: pure matrix algebra. Intended axiom footprint `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped Matrix

variable {n q : ℕ}

/-- The Gram of `Q = A` with the row `w` appended, split as a `Fin n ⊕ Unit` block matrix:
`Q Qᵀ = fromBlocks (A Aᵀ) (A·w col) ((A·w) row) (w⬝w)`. -/
theorem gram_row_snoc_eq_fromBlocks (A : Matrix (Fin n) (Fin q) ℝ) (w : Fin q → ℝ) :
    (Matrix.of (Sum.elim A (fun _ : Unit => w))) *
        (Matrix.of (Sum.elim A (fun _ : Unit => w)))ᵀ
      = fromBlocks (A * Aᵀ)
          (Matrix.of fun i (_ : Unit) => (A *ᵥ w) i)
          (Matrix.of fun (_ : Unit) j => (A *ᵥ w) j)
          (Matrix.of fun (_ : Unit) (_ : Unit) => w ⬝ᵥ w) := by
  ext i j
  rcases i with a | u <;> rcases j with b | v <;>
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Sum.elim_inl,
        Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.mulVec, dotProduct]
      try exact Finset.sum_congr rfl fun k _ => by ring

/-- **Gram Schur-complement determinant recursion (algebraic form).** With `A Aᵀ` invertible,
appending a row `w` scales the Gram determinant by the Schur-complement scalar. -/
theorem det_gram_row_snoc (A : Matrix (Fin n) (Fin q) ℝ) (w : Fin q → ℝ)
    [Invertible (A * Aᵀ)] :
    (Matrix.of (Sum.elim A (fun _ : Unit => w)) *
        (Matrix.of (Sum.elim A (fun _ : Unit => w)))ᵀ).det
      = (A * Aᵀ).det * (w ⬝ᵥ w - (A *ᵥ w) ⬝ᵥ (⅟(A * Aᵀ) *ᵥ (A *ᵥ w))) := by
  rw [gram_row_snoc_eq_fromBlocks A w, det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique, Matrix.sub_apply, Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec]

end DLNFibre.DLN.RLCT
