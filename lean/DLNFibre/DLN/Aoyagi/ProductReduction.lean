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

/-- An upper unitriangular left multiplier preserves an identity top-left corner. -/
theorem upperUnitriangular_mul_fromBlocks_one_zero {r m n : ℕ}
    (F : Matrix (Fin r) (Fin m) K) (B : Matrix (Fin r) (Fin n) K)
    (D : Matrix (Fin m) (Fin n) K) :
    fromBlocks (1 : Matrix (Fin r) (Fin r) K) (-F) 0 1
        * fromBlocks (1 : Matrix (Fin r) (Fin r) K) B 0 D =
      fromBlocks (1 : Matrix (Fin r) (Fin r) K) (B - F * D) 0 D := by
  rw [fromBlocks_multiply]
  simp [sub_eq_add_neg]

/-- An indexed version of `upperUnitriangular_mul_fromBlocks_one_zero`. -/
theorem upperUnitriangular_mul_fromBlocks_one_zero_indexed
    {ι μ ν : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
    (F : Matrix ι μ K) (B : Matrix ι ν K) (D : Matrix μ ν K) :
    fromBlocks (1 : Matrix ι ι K) (-F) 0 1
        * fromBlocks (1 : Matrix ι ι K) B 0 D =
      fromBlocks (1 : Matrix ι ι K) (B - F * D) 0 D := by
  rw [fromBlocks_multiply]
  simp [sub_eq_add_neg]

/-- An upper unitriangular left multiplier preserves existence of an identity-corner chart form. -/
theorem exists_fromBlocks_one_zero_of_upperUnitriangular_mul {r m n : ℕ}
    (F : Matrix (Fin r) (Fin m) K)
    (M : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin n) K)
    (hM : ∃ B : Matrix (Fin r) (Fin n) K, ∃ D : Matrix (Fin m) (Fin n) K,
      M = fromBlocks (1 : Matrix (Fin r) (Fin r) K) B 0 D) :
    ∃ B' : Matrix (Fin r) (Fin n) K, ∃ D' : Matrix (Fin m) (Fin n) K,
      fromBlocks (1 : Matrix (Fin r) (Fin r) K) (-F) 0 1 * M =
        fromBlocks (1 : Matrix (Fin r) (Fin r) K) B' 0 D' := by
  rcases hM with ⟨B, D, rfl⟩
  exact ⟨B - F * D, D, upperUnitriangular_mul_fromBlocks_one_zero F B D⟩

/-- Indexed chart-form preservation under an upper unitriangular left multiplier. -/
theorem exists_fromBlocks_one_zero_of_upperUnitriangular_mul_indexed
    {ι μ ν : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
    (F : Matrix ι μ K) (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K)
    (hM : ∃ B : Matrix ι ν K, ∃ D : Matrix μ ν K,
      M = fromBlocks (1 : Matrix ι ι K) B 0 D) :
    ∃ B' : Matrix ι ν K, ∃ D' : Matrix μ ν K,
      fromBlocks (1 : Matrix ι ι K) (-F) 0 1 * M =
        fromBlocks (1 : Matrix ι ι K) B' 0 D' := by
  rcases hM with ⟨B, D, rfl⟩
  exact ⟨B - F * D, D, upperUnitriangular_mul_fromBlocks_one_zero_indexed F B D⟩

/-- The selected top-left corner of a block matrix. -/
def topLeftCorner {ι μ ν : Type*} (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Matrix ι ι K :=
  M.submatrix Sum.inl Sum.inl

/-- The upper-right block of a block matrix. -/
def upperRightBlock {ι μ ν : Type*} (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Matrix ι ν K :=
  M.submatrix Sum.inl Sum.inr

/-- The lower-right block of a block matrix. -/
def lowerRightBlock {ι μ ν : Type*} (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Matrix μ ν K :=
  M.submatrix Sum.inr Sum.inr

/-- A block matrix with identity top-left corner and zero lower-left block. -/
def identityCornerForm {ι μ ν : Type*} [DecidableEq ι]
    (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Prop :=
  ∃ B : Matrix ι ν K, ∃ D : Matrix μ ν K,
    M = fromBlocks (1 : Matrix ι ι K) B 0 D

/-- Algebraic determinant-chart membership for the selected top-left corner. -/
def identityCornerDetChart {ι μ ν : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Prop :=
  IsUnit (topLeftCorner M).det

/-- In identity-corner form, the selected top-left corner is exactly `1`. -/
theorem topLeftCorner_eq_one_of_identityCornerForm
    {ι μ ν : Type*} [DecidableEq ι] {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K}
    (hM : identityCornerForm M) :
    topLeftCorner M = (1 : Matrix ι ι K) := by
  rcases hM with ⟨B, D, rfl⟩
  rfl

/-- Identity-corner form lies in the determinant chart of the selected top-left block. -/
theorem identityCornerDetChart_of_identityCornerForm
    {ι μ ν : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K}
    (hM : identityCornerForm M) :
    identityCornerDetChart M := by
  rw [identityCornerDetChart, topLeftCorner_eq_one_of_identityCornerForm hM]
  simp

/-- Upper-unitriangular multiplication preserves identity-corner form. -/
theorem identityCornerForm_upperUnitriangular_mul
    {ι μ ν : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
    (F : Matrix ι μ K) {M : Matrix (ι ⊕ μ) (ι ⊕ ν) K}
    (hM : identityCornerForm M) :
    identityCornerForm
      (fromBlocks (1 : Matrix ι ι K) (-F) 0 (1 : Matrix μ μ K) * M) :=
  exists_fromBlocks_one_zero_of_upperUnitriangular_mul_indexed F M hM

/-- Explicit one-edge right elimination for a witnessed identity-corner block matrix. -/
theorem productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed
    {R : Type*} [NonAssocRing R]
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [Fintype ν] [DecidableEq ν]
    (C1 : Matrix ρ ρ R) (Dprev : Matrix π μ R)
    (B : Matrix ρ ν R) (Dnext : Matrix μ ν R) :
    fromBlocks C1 0 0 Dprev *
          fromBlocks (1 : Matrix ρ ρ R) B 0 Dnext *
          fromBlocks (1 : Matrix ρ ρ R) (-B) 0 (1 : Matrix ν ν R) =
        fromBlocks C1 0 0 (Dprev * Dnext) := by
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp

/-- One-edge right elimination for a matrix explicitly equal to identity-corner form. -/
theorem productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed
    {R : Type*} [NonAssocRing R]
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [Fintype ν] [DecidableEq ν]
    (C1 : Matrix ρ ρ R) (Dprev : Matrix π μ R)
    {M : Matrix (ρ ⊕ μ) (ρ ⊕ ν) R}
    (B : Matrix ρ ν R) (Dnext : Matrix μ ν R)
    (hM : M = fromBlocks (1 : Matrix ρ ρ R) B 0 Dnext) :
    fromBlocks C1 0 0 Dprev * M *
          fromBlocks (1 : Matrix ρ ρ R) (-B) 0 (1 : Matrix ν ν R) =
        fromBlocks C1 0 0 (Dprev * Dnext) := by
  rw [hM]
  exact productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed
    C1 Dprev B Dnext

/-- A block-diagonal prefix times an identity-corner edge can be right-eliminated. -/
theorem productReduction_blockDiagonal_mul_identityCornerForm_rightElim
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [Fintype ν] [DecidableEq ν]
    (C1 : Matrix ρ ρ K) (Dprev : Matrix π μ K)
    {M : Matrix (ρ ⊕ μ) (ρ ⊕ ν) K}
    (hM : identityCornerForm M) :
    ∃ B : Matrix ρ ν K, ∃ Dnext : Matrix μ ν K,
      fromBlocks C1 0 0 Dprev * M *
          fromBlocks (1 : Matrix ρ ρ K) (-B) 0 (1 : Matrix ν ν K) =
        fromBlocks C1 0 0 (Dprev * Dnext) := by
  rcases hM with ⟨B, Dnext, hM⟩
  refine ⟨B, Dnext, ?_⟩
  exact productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed
    C1 Dprev B Dnext hM

/-- Canonical one-edge right elimination using the actual upper/lower-right blocks. -/
theorem productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [Fintype ν] [DecidableEq ν]
    (C1 : Matrix ρ ρ K) (Dprev : Matrix π μ K)
    {M : Matrix (ρ ⊕ μ) (ρ ⊕ ν) K}
    (hM : identityCornerForm M) :
    fromBlocks C1 0 0 Dprev * M *
          fromBlocks (1 : Matrix ρ ρ K) (-(upperRightBlock M)) 0 (1 : Matrix ν ν K) =
        fromBlocks C1 0 0 (Dprev * lowerRightBlock M) := by
  rcases hM with ⟨B, Dnext, rfl⟩
  simpa [upperRightBlock, lowerRightBlock] using
    productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed
      C1 Dprev B Dnext

/-- Canonical right elimination after an accumulated upper-unitriangular left multiplier. -/
theorem productReduction_blockDiagonal_mul_unitriangular_identityCornerForm_rightElim
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ] [DecidableEq μ]
    [Fintype ν] [DecidableEq ν]
    (C1 : Matrix ρ ρ K) (Dprev : Matrix π μ K) (F : Matrix ρ μ K)
    {M : Matrix (ρ ⊕ μ) (ρ ⊕ ν) K}
    (hM : identityCornerForm M) :
    let M' := fromBlocks (1 : Matrix ρ ρ K) (-F) 0 (1 : Matrix μ μ K) * M
    fromBlocks C1 0 0 Dprev * M' *
          fromBlocks (1 : Matrix ρ ρ K) (-(upperRightBlock M')) 0 (1 : Matrix ν ν K) =
        fromBlocks C1 0 0 (Dprev * lowerRightBlock M') := by
  dsimp
  exact productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix
    C1 Dprev (identityCornerForm_upperUnitriangular_mul F hM)

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

/-- Indexed version of `nonsing_inv_mul_left_factor`. -/
private theorem nonsing_inv_mul_left_factor_indexed {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (C1 A1 : Matrix ρ ρ K) (hC1 : IsUnit C1.det) (hA1 : IsUnit A1.det) :
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

/-- Indexed chart-local algebraic induction step in Aoyagi's block product reduction. -/
theorem productReduction_chartLocalInductionStep_fromBlocks_indexed
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π] [DecidableEq π]
    [Fintype μ] [Fintype ν] [DecidableEq ν]
    (C1 : Matrix ρ ρ K) (D : Matrix π μ K)
    (A1 : Matrix ρ ρ K) (A2 : Matrix ρ ν K)
    (A3 : Matrix μ ρ K) (A4 : Matrix μ ν K)
    (hC1 : IsUnit C1.det) (hA1 : IsUnit A1.det) :
    fromBlocks (1 : Matrix ρ ρ K) 0 (-(D * A3 * (C1 * A1)⁻¹)) 1
        * (fromBlocks C1 0 0 D * fromBlocks A1 A2 A3 A4)
        * fromBlocks (1 : Matrix ρ ρ K) (-(A1⁻¹ * A2)) 0 1 =
      fromBlocks (C1 * A1) 0 0 (D * (A4 - A3 * A1⁻¹ * A2)) := by
  have hC1A1 : IsUnit (C1 * A1).det := by
    simpa [Matrix.det_mul] using hC1.mul hA1
  have hInvC1 : (C1 * A1)⁻¹ * C1 = A1⁻¹ :=
    nonsing_inv_mul_left_factor_indexed C1 A1 hC1 hA1
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
    fromBlocks (1 : Matrix ρ ρ K) 0 (-(D * A3 * (C1 * A1)⁻¹)) 1
        * (fromBlocks C1 0 0 D * fromBlocks A1 A2 A3 A4)
        * fromBlocks (1 : Matrix ρ ρ K) (-(A1⁻¹ * A2)) 0 1
        =
      fromBlocks (1 : Matrix ρ ρ K) 0 (-(D * A3 * (C1 * A1)⁻¹)) 1
        * fromBlocks (C1 * A1) (C1 * A2) (D * A3) (D * A4)
        * fromBlocks (1 : Matrix ρ ρ K) (-(A1⁻¹ * A2)) 0 1 := by
          rw [hPrefix]
    _ = fromBlocks (C1 * A1) 0 0
          (D * A4 - (D * A3) * (C1 * A1)⁻¹ * (C1 * A2)) := by
      simpa [hRight] using
        schurComplement_blockElim_fromBlocks_indexed
          (C1 * A1) (C1 * A2) (D * A3) (D * A4) hC1A1
    _ = fromBlocks (C1 * A1) 0 0 (D * (A4 - A3 * A1⁻¹ * A2)) := by
      rw [hSchur]

end InductionStep

end Aoyagi
end DLN
end DLNFibre
