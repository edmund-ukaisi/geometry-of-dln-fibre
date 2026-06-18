import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Aoyagi block-elimination identities

This file formalises the two algebraic block identities in Aoyagi's Lemma 2.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

variable {K : Type*} [CommRing K]

/-- Left block elimination exposes the Schur complement in the lower-right block. -/
theorem schurComplement_leftBlockElim_fromBlocks {r p q : ℕ}
    (A1 : Matrix (Fin r) (Fin r) K) (A2 : Matrix (Fin r) (Fin q) K)
    (A3 : Matrix (Fin p) (Fin r) K) (A4 : Matrix (Fin p) (Fin q) K)
    (hA1 : IsUnit A1.det) :
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (-(A3 * A1⁻¹)) 1
        * fromBlocks A1 A2 A3 A4 =
      fromBlocks A1 A2 0 (A4 - A3 * A1⁻¹ * A2) := by
  rw [fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA1, sub_eq_add_neg, add_comm]

/-- Two-sided block elimination produces a block diagonal matrix with Schur complement. -/
theorem schurComplement_blockElim_fromBlocks {r p q : ℕ}
    (A1 : Matrix (Fin r) (Fin r) K) (A2 : Matrix (Fin r) (Fin q) K)
    (A3 : Matrix (Fin p) (Fin r) K) (A4 : Matrix (Fin p) (Fin q) K)
    (hA1 : IsUnit A1.det) :
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (-(A3 * A1⁻¹)) 1
        * fromBlocks A1 A2 A3 A4
        * fromBlocks (1 : Matrix (Fin r) (Fin r) K) (-(A1⁻¹ * A2)) 0 1 =
      fromBlocks A1 0 0 (A4 - A3 * A1⁻¹ * A2) := by
  rw [schurComplement_leftBlockElim_fromBlocks A1 A2 A3 A4 hA1]
  rw [fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left A1 A2 hA1, sub_eq_add_neg]

end Aoyagi
end DLN
end DLNFibre
