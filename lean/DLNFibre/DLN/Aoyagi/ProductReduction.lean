import DLNFibre.DLN.Aoyagi.BlockElimination

/-!
# Aoyagi product-reduction induction step

This file formalises the chart-local block algebra used in one induction step
of Aoyagi's product reduction.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

section InductionStep

variable {K : Type*} [CommRing K]

/-- The determinant-unit chart hypotheses are inhabited by identity corners. -/
example {r : ℕ} : IsUnit (1 : Matrix (Fin r) (Fin r) K).det := by
  simp

/-- The inverse of a product corner cancels the already-invertible left factor. -/
private theorem nonsing_inv_mul_left_factor {r : ℕ}
    (C1 A1 : Matrix (Fin r) (Fin r) K) (hC1 : IsUnit C1.det) (hA1 : IsUnit A1.det) :
    (C1 * A1)⁻¹ * C1 = A1⁻¹ := by
  have hC1A1 : IsUnit (C1 * A1).det := by
    simpa [Matrix.det_mul] using hC1.mul hA1
  refine Matrix.left_inv_eq_left_inv (A := A1) ?_ (Matrix.nonsing_inv_mul A1 hA1)
  calc
    ((C1 * A1)⁻¹ * C1) * A1 = (C1 * A1)⁻¹ * (C1 * A1) := by
      rw [Matrix.mul_assoc]
    _ = 1 := Matrix.nonsing_inv_mul (C1 * A1) hC1A1

/-- One chart-local algebraic induction step in Aoyagi's block product reduction. -/
theorem productReduction_chartLocalInductionStep_fromBlocks {r p m n : ℕ}
    (C1 : Matrix (Fin r) (Fin r) K) (D : Matrix (Fin p) (Fin m) K)
    (A1 : Matrix (Fin r) (Fin r) K) (A2 : Matrix (Fin r) (Fin n) K)
    (A3 : Matrix (Fin m) (Fin r) K) (A4 : Matrix (Fin m) (Fin n) K)
    (hC1 : IsUnit C1.det) (hA1 : IsUnit A1.det) :
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (-(D * A3 * (C1 * A1)⁻¹)) 1
        * (fromBlocks C1 0 0 D * fromBlocks A1 A2 A3 A4)
        * fromBlocks (1 : Matrix (Fin r) (Fin r) K) (-(A1⁻¹ * A2)) 0 1 =
      fromBlocks (C1 * A1) 0 0 (D * (A4 - A3 * A1⁻¹ * A2)) := by
  have hC1A1 : IsUnit (C1 * A1).det := by
    simpa [Matrix.det_mul] using hC1.mul hA1
  have hInvC1 : (C1 * A1)⁻¹ * C1 = A1⁻¹ :=
    nonsing_inv_mul_left_factor C1 A1 hC1 hA1
  have hRight : (C1 * A1)⁻¹ * (C1 * A2) = A1⁻¹ * A2 := by
    calc
      (C1 * A1)⁻¹ * (C1 * A2) = ((C1 * A1)⁻¹ * C1) * A2 := by
        rw [Matrix.mul_assoc]
      _ = A1⁻¹ * A2 := by rw [hInvC1]
  have hPrefix :
      fromBlocks C1 0 0 D * fromBlocks A1 A2 A3 A4 =
        fromBlocks (C1 * A1) (C1 * A2) (D * A3) (D * A4) := by
    rw [fromBlocks_multiply]
    simp
  have hSchur :
      D * A4 - (D * A3) * (C1 * A1)⁻¹ * (C1 * A2) =
        D * (A4 - A3 * A1⁻¹ * A2) := by
    calc
      D * A4 - (D * A3) * (C1 * A1)⁻¹ * (C1 * A2)
          = D * A4 - (D * A3) * ((C1 * A1)⁻¹ * (C1 * A2)) := by
        rw [Matrix.mul_assoc]
      _ = D * A4 - (D * A3) * (A1⁻¹ * A2) := by rw [hRight]
      _ = D * A4 - D * (A3 * A1⁻¹ * A2) := by
        rw [Matrix.mul_assoc D A3 (A1⁻¹ * A2), ← Matrix.mul_assoc A3 A1⁻¹ A2]
      _ = D * (A4 - A3 * A1⁻¹ * A2) := by rw [Matrix.mul_sub]
  calc
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (-(D * A3 * (C1 * A1)⁻¹)) 1
        * (fromBlocks C1 0 0 D * fromBlocks A1 A2 A3 A4)
        * fromBlocks (1 : Matrix (Fin r) (Fin r) K) (-(A1⁻¹ * A2)) 0 1
        =
      fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 (-(D * A3 * (C1 * A1)⁻¹)) 1
        * fromBlocks (C1 * A1) (C1 * A2) (D * A3) (D * A4)
        * fromBlocks (1 : Matrix (Fin r) (Fin r) K) (-(A1⁻¹ * A2)) 0 1 := by
          rw [hPrefix]
    _ = fromBlocks (C1 * A1) 0 0
          (D * A4 - (D * A3) * (C1 * A1)⁻¹ * (C1 * A2)) := by
      simpa [hRight] using
        schurComplement_blockElim_fromBlocks (C1 * A1) (C1 * A2) (D * A3) (D * A4) hC1A1
    _ = fromBlocks (C1 * A1) 0 0 (D * (A4 - A3 * A1⁻¹ * A2)) := by
      rw [hSchur]

end InductionStep

end Aoyagi
end DLN
end DLNFibre
