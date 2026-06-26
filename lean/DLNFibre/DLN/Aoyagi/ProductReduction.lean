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

/-- Deterministic data carried by one suffix state in chart-local product reduction. -/
structure ChartLocalSuffixState {N : ℕ}
    (ρ : Type*) (κ : Fin (N + 1) → Type*) (K : Type*)
    (j i : Fin (N + 1)) where
  L : Matrix (ρ ⊕ κ j) (ρ ⊕ κ j) K
  B : Matrix ρ (κ i) K
  Ctop : Matrix ρ ρ K
  D : Matrix (κ j) (κ i) K

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

/-- Indexed multiplication of lower unitriangular block matrices. -/
theorem lowerUnitriangular_mul_fromBlocks_one_zero_indexed
    {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
    (F G : Matrix μ ι K) :
    fromBlocks (1 : Matrix ι ι K) 0 F (1 : Matrix μ μ K) *
        fromBlocks (1 : Matrix ι ι K) 0 G (1 : Matrix μ μ K) =
      fromBlocks (1 : Matrix ι ι K) 0 (F + G) (1 : Matrix μ μ K) := by
  rw [fromBlocks_multiply]
  simp

/-- Subtracting the rank-model block after triangular endpoint reduction gives
the displayed product-difference block matrix. -/
theorem triangularBlockProductDifference_fromBlocks_indexed
    {ι μ ν : Type*} [Fintype ι] [Fintype μ] [Fintype ν]
    [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
    (F2 : Matrix ι ν K) (F3 : Matrix μ ι K)
    (Ctop : Matrix ι ι K) (D : Matrix μ ν K)
    (T : Matrix (ι ⊕ μ) (ι ⊕ ν) K)
    (htri :
      fromBlocks (1 : Matrix ι ι K) 0 F3 (1 : Matrix μ μ K) * T *
        fromBlocks (1 : Matrix ι ι K) F2 0 (1 : Matrix ν ν K) =
          fromBlocks Ctop 0 0 D) :
    fromBlocks (1 : Matrix ι ι K) 0 F3 (1 : Matrix μ μ K) *
        (T - fromBlocks (1 : Matrix ι ι K) 0
          (0 : Matrix μ ι K) (0 : Matrix μ ν K)) *
        fromBlocks (1 : Matrix ι ι K) F2 0 (1 : Matrix ν ν K) =
      fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2) := by
  let L : Matrix (ι ⊕ μ) (ι ⊕ μ) K :=
    fromBlocks (1 : Matrix ι ι K) 0 F3 (1 : Matrix μ μ K)
  let Rmat : Matrix (ι ⊕ ν) (ι ⊕ ν) K :=
    fromBlocks (1 : Matrix ι ι K) F2 0 (1 : Matrix ν ν K)
  let T0 : Matrix (ι ⊕ μ) (ι ⊕ ν) K :=
    fromBlocks (1 : Matrix ι ι K) 0 (0 : Matrix μ ι K) (0 : Matrix μ ν K)
  have hsplit : L * (T - T0) * Rmat = L * T * Rmat - L * T0 * Rmat := by
    simp [sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hT0 :
      L * T0 * Rmat = fromBlocks (1 : Matrix ι ι K) F2 F3 (F3 * F2) := by
    simp [L, T0, Rmat, fromBlocks_multiply]
  change L * (T - T0) * Rmat =
    fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2)
  calc
    L * (T - T0) * Rmat = L * T * Rmat - L * T0 * Rmat := hsplit
    _ = fromBlocks Ctop 0 0 D -
        fromBlocks (1 : Matrix ι ι K) F2 F3 (F3 * F2) := by
      rw [hT0]
      simpa [L, Rmat] using
        congrArg
          (fun M ↦ M - fromBlocks (1 : Matrix ι ι K) F2 F3 (F3 * F2))
          htri
    _ = fromBlocks (Ctop - 1) (-F2) (-F3) (D - F3 * F2) := by
      ext (i | i) (j | j) <;> simp

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

/-- The lower-left block of a block matrix. -/
def lowerLeftBlock {ι μ ν : Type*} (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Matrix μ ι K :=
  M.submatrix Sum.inr Sum.inl

/-- The lower-right block of a block matrix. -/
def lowerRightBlock {ι μ ν : Type*} (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Matrix μ ν K :=
  M.submatrix Sum.inr Sum.inr

omit [CommRing K] in
/-- Reassemble a block matrix from its four selected corners. -/
theorem fromBlocks_corners {ι μ ν : Type*} (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) :
    fromBlocks (topLeftCorner M) (upperRightBlock M) (lowerLeftBlock M)
      (lowerRightBlock M) = M := by
  ext (i | i) (j | j) <;> rfl

omit [CommRing K] in
@[simp]
theorem topLeftCorner_fromBlocks {ι μ ν : Type*}
    (A : Matrix ι ι K) (B : Matrix ι ν K) (C : Matrix μ ι K) (D : Matrix μ ν K) :
    topLeftCorner (fromBlocks A B C D) = A := by
  ext i j
  simp [topLeftCorner]

omit [CommRing K] in
@[simp]
theorem upperRightBlock_fromBlocks {ι μ ν : Type*}
    (A : Matrix ι ι K) (B : Matrix ι ν K) (C : Matrix μ ι K) (D : Matrix μ ν K) :
    upperRightBlock (fromBlocks A B C D) = B := by
  ext i j
  simp [upperRightBlock]

omit [CommRing K] in
@[simp]
theorem lowerLeftBlock_fromBlocks {ι μ ν : Type*}
    (A : Matrix ι ι K) (B : Matrix ι ν K) (C : Matrix μ ι K) (D : Matrix μ ν K) :
    lowerLeftBlock (fromBlocks A B C D) = C := by
  ext i j
  simp [lowerLeftBlock]

omit [CommRing K] in
@[simp]
theorem lowerRightBlock_fromBlocks {ι μ ν : Type*}
    (A : Matrix ι ι K) (B : Matrix ι ν K) (C : Matrix μ ι K) (D : Matrix μ ν K) :
    lowerRightBlock (fromBlocks A B C D) = D := by
  ext i j
  simp [lowerRightBlock]

/-- A block matrix with identity top-left corner and zero lower-left block. -/
def identityCornerForm {ι μ ν : Type*} [DecidableEq ι]
    (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Prop :=
  ∃ B : Matrix ι ν K, ∃ D : Matrix μ ν K,
    M = fromBlocks (1 : Matrix ι ι K) B 0 D

/-- Algebraic determinant-chart membership for the selected top-left corner. -/
def identityCornerDetChart {ι μ ν : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Prop :=
  IsUnit (topLeftCorner M).det

/-- The Schur residual of the lower-right corner in the selected determinant chart. -/
def schurResidualBlock {ι μ ν : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K) : Matrix μ ν K :=
  lowerRightBlock M - lowerLeftBlock M * (topLeftCorner M)⁻¹ * upperRightBlock M

/-- If the upper-right block is zero, the Schur residual is the lower-right block. -/
theorem schurResidualBlock_fromBlocks_upperRight_zero
    {ι μ ν : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (C : Matrix μ ι K) (D : Matrix μ ν K) :
    schurResidualBlock (fromBlocks A (0 : Matrix ι ν K) C D) = D := by
  ext i j
  simp [schurResidualBlock, topLeftCorner, upperRightBlock, lowerLeftBlock,
    lowerRightBlock, Matrix.mul_apply]

/-- If the lower-left block is zero, the Schur residual is the lower-right block. -/
theorem schurResidualBlock_fromBlocks_lowerLeft_zero
    {ι μ ν : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (B : Matrix ι ν K) (D : Matrix μ ν K) :
    schurResidualBlock (fromBlocks A B (0 : Matrix μ ι K) D) = D := by
  ext i j
  simp [schurResidualBlock, topLeftCorner, upperRightBlock, lowerLeftBlock,
    lowerRightBlock, Matrix.mul_apply]

/-- Reassembling a block matrix from its one-step Schur readbacks recovers the
original matrix on the selected determinant chart. -/
theorem fromBlocks_schurReadbacks_eq
    {ι μ ν : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (ι ⊕ μ) (ι ⊕ ν) K)
    (hA1 : IsUnit (topLeftCorner M).det) :
    fromBlocks (topLeftCorner M)
        (-(topLeftCorner M * (-((topLeftCorner M)⁻¹ * upperRightBlock M))))
        (lowerLeftBlock M)
        (schurResidualBlock M -
          lowerLeftBlock M * (-((topLeftCorner M)⁻¹ * upperRightBlock M))) =
      M := by
  have hneg : - -upperRightBlock M = upperRightBlock M := neg_neg _
  rw [← fromBlocks_corners (K := K) M]
  simp [schurResidualBlock, hA1, Matrix.mul_assoc, sub_eq_add_neg, add_assoc, hneg]

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

/-- Opposite upper-unitriangular right multipliers cancel. -/
theorem upperUnitriangular_neg_mul_upperUnitriangular
    {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    (B : Matrix ι μ K) :
    fromBlocks (1 : Matrix ι ι K) (-B) 0 (1 : Matrix μ μ K) *
        fromBlocks (1 : Matrix ι ι K) B 0 (1 : Matrix μ μ K) = 1 := by
  ext (i | i) (j | j) <;>
    simp [fromBlocks_multiply, Matrix.one_apply]

/-- The double-negated form of the upper-unitriangular cancellation identity. -/
theorem upperUnitriangular_neg_mul_upperUnitriangular_neg_neg
    {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    (B : Matrix ι μ K) :
    fromBlocks (1 : Matrix ι ι K) (-B) 0 (1 : Matrix μ μ K) *
        fromBlocks (1 : Matrix ι ι K) (-(-B)) 0 (1 : Matrix μ μ K) = 1 := by
  ext (i | i) (j | j) <;>
    simp [fromBlocks_multiply, Matrix.one_apply]

/-- One abstract suffix-induction step for identity-corner right elimination. -/
theorem productReduction_identityCorner_suffixStep_rightElim
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (Ptail : Matrix (ρ ⊕ π) (ρ ⊕ μ) K)
    (Bprev : Matrix ρ μ K) (Dprev : Matrix π μ K)
    {E : Matrix (ρ ⊕ μ) (ρ ⊕ ν) K}
    (hE : identityCornerForm E)
    (hPtail : Ptail *
        fromBlocks (1 : Matrix ρ ρ K) (-Bprev) 0 (1 : Matrix μ μ K) =
          fromBlocks (1 : Matrix ρ ρ K) 0 0 Dprev) :
    ∃ B : Matrix ρ ν K, ∃ D : Matrix π ν K,
      Ptail * E * fromBlocks (1 : Matrix ρ ρ K) (-B) 0 (1 : Matrix ν ν K) =
        fromBlocks (1 : Matrix ρ ρ K) 0 0 D := by
  let M' : Matrix (ρ ⊕ μ) (ρ ⊕ ν) K :=
    fromBlocks (1 : Matrix ρ ρ K) (-(-Bprev)) 0 (1 : Matrix μ μ K) * E
  have hM' : identityCornerForm M' := by
    exact identityCornerForm_upperUnitriangular_mul (K := K) (F := -Bprev) hE
  have hfactor : E =
      fromBlocks (1 : Matrix ρ ρ K) (-Bprev) 0 (1 : Matrix μ μ K) * M' := by
    calc
      E = (1 : Matrix (ρ ⊕ μ) (ρ ⊕ μ) K) * E := by rw [Matrix.one_mul]
      _ = (fromBlocks (1 : Matrix ρ ρ K) (-Bprev) 0 (1 : Matrix μ μ K) *
              fromBlocks (1 : Matrix ρ ρ K) (-(-Bprev)) 0 (1 : Matrix μ μ K)) * E := by
            rw [upperUnitriangular_neg_mul_upperUnitriangular_neg_neg Bprev]
      _ = fromBlocks (1 : Matrix ρ ρ K) (-Bprev) 0 (1 : Matrix μ μ K) * M' := by
            rw [Matrix.mul_assoc]
  refine ⟨upperRightBlock M', Dprev * lowerRightBlock M', ?_⟩
  calc
    Ptail * E *
        fromBlocks (1 : Matrix ρ ρ K) (-(upperRightBlock M')) 0 (1 : Matrix ν ν K)
        =
      Ptail *
          (fromBlocks (1 : Matrix ρ ρ K) (-Bprev) 0 (1 : Matrix μ μ K) * M') *
        fromBlocks (1 : Matrix ρ ρ K) (-(upperRightBlock M')) 0 (1 : Matrix ν ν K) := by
          rw [hfactor]
    _ =
      (Ptail * fromBlocks (1 : Matrix ρ ρ K) (-Bprev) 0 (1 : Matrix μ μ K)) * M' *
        fromBlocks (1 : Matrix ρ ρ K) (-(upperRightBlock M')) 0 (1 : Matrix ν ν K) := by
          rw [← Matrix.mul_assoc]
    _ =
      fromBlocks (1 : Matrix ρ ρ K) 0 0 Dprev * M' *
        fromBlocks (1 : Matrix ρ ρ K) (-(upperRightBlock M')) 0 (1 : Matrix ν ν K) := by
          rw [hPtail]
    _ = fromBlocks (1 : Matrix ρ ρ K) 0 0 (Dprev * lowerRightBlock M') :=
      productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix
        (1 : Matrix ρ ρ K) Dprev hM'

/-- Abstract suffix-chain right elimination for identity-corner edge matrices. -/
theorem productReduction_identityCorner_suffixChain_rightElim
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hPproof : ∀ {i j : Fin (N + 1)} (h h' : i ≤ j), P i j h = P i j h')
    (hself : ∀ j : Fin (N + 1), P j j le_rfl = 1)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    (hE : ∀ p, identityCornerForm (E p)) :
    ∀ i j : Fin (N + 1), ∀ hij : i ≤ j,
      ∃ B : Matrix ρ (κ i) K, ∃ D : Matrix (κ j) (κ i) K,
        P i j hij * fromBlocks (1 : Matrix ρ ρ K) (-B) 0 (1 : Matrix (κ i) (κ i) K) =
          fromBlocks (1 : Matrix ρ ρ K) 0 0 D := by
  intro i j hij
  let motive : (m : ℕ) → m ≤ j.val → Prop := fun m hmj ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmj j.isLt⟩
    ∃ B : Matrix ρ (κ im) K, ∃ D : Matrix (κ j) (κ im) K,
      P im j (Fin.val_fin_le.mpr hmj) *
          fromBlocks (1 : Matrix ρ ρ K) (-B) 0 (1 : Matrix (κ im) (κ im) K) =
        fromBlocks (1 : Matrix ρ ρ K) 0 0 D
  have hbase : motive j.val le_rfl := by
    dsimp [motive]
    refine ⟨0, 1, ?_⟩
    rw [hPproof (Fin.val_fin_le.mpr (le_rfl : j.val ≤ j.val)) le_rfl, hself j,
      Matrix.one_mul]
    simp
  have hstep : ∀ m (hms : m + 1 ≤ j.val),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (hms.trans_lt j.isLt)⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have ih' :
        ∃ B : Matrix ρ (κ p.succ) K, ∃ D : Matrix (κ j) (κ p.succ) K,
          P p.succ j hpj *
              fromBlocks (1 : Matrix ρ ρ K) (-B) 0 (1 : Matrix (κ p.succ) (κ p.succ) K) =
            fromBlocks (1 : Matrix ρ ρ K) 0 0 D := by
      simpa [motive, p, hpj] using ih
    rcases ih' with ⟨Bprev, Dprev, hprev⟩
    rcases productReduction_identityCorner_suffixStep_rightElim
        (K := K) (Ptail := P p.succ j hpj) Bprev Dprev (hE p) hprev with
      ⟨B, D, hD⟩
    have hcanon :
        ∃ B : Matrix ρ (κ p.castSucc) K, ∃ D : Matrix (κ j) (κ p.castSucc) K,
          P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) *
              fromBlocks (1 : Matrix ρ ρ K) (-B) 0
                (1 : Matrix (κ p.castSucc) (κ p.castSucc) K) =
            fromBlocks (1 : Matrix ρ ρ K) 0 0 D := by
      refine ⟨B, D, ?_⟩
      rw [hsuccRight p j hpj]
      exact hD
    simpa [motive, p, hpj] using hcanon
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hij)
  have hcanon' :
      ∃ B : Matrix ρ (κ i) K, ∃ D : Matrix (κ j) (κ i) K,
        P i j (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij)) *
            fromBlocks (1 : Matrix ρ ρ K) (-B) 0 (1 : Matrix (κ i) (κ i) K) =
          fromBlocks (1 : Matrix ρ ρ K) 0 0 D := by
    simpa [motive] using hcanon
  rcases hcanon' with ⟨B, D, hD⟩
  refine ⟨B, D, ?_⟩
  rwa [hPproof hij (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij))]

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

/-- Raw one-step variables for the p. 13 triangular product-reduction
coordinate change.

The fields `D`, `F3`, `A1`, and `A3` are retained as chart variables; in
particular the inverse formulas below never invert `D`. -/
structure ProductReductionStepRawCoordinates
    (ρ π μ ν : Type*) (K : Type*) where
  C1 : Matrix ρ ρ K
  D : Matrix π μ K
  F3 : Matrix π ρ K
  A1 : Matrix ρ ρ K
  A2 : Matrix ρ ν K
  A3 : Matrix μ ρ K
  A4 : Matrix μ ν K

/-- Target one-step variables for the p. 13 triangular product-reduction
coordinate change.

`C` is the new residual block `A4 - A3 A1^{-1} A2`; the fields `D`, `A1`, and
`A3` are passive variables. -/
structure ProductReductionStepChartCoordinates
    (ρ π μ ν : Type*) (K : Type*) where
  Ctop : Matrix ρ ρ K
  D : Matrix π μ K
  A1 : Matrix ρ ρ K
  A3 : Matrix μ ρ K
  F2 : Matrix ρ ν K
  F3 : Matrix π ρ K
  C : Matrix μ ν K

namespace ProductReductionStepRawCoordinates

/-- Determinant-chart domain for the raw one-step variables. -/
def detChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) : Prop :=
  IsUnit x.C1.det ∧ IsUnit x.A1.det

/-- Forward p. 13 triangular coordinate change for one product-reduction step. -/
def toChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν K) :
    ProductReductionStepChartCoordinates ρ π μ ν K where
  Ctop := x.C1 * x.A1
  D := x.D
  A1 := x.A1
  A3 := x.A3
  F2 := -(x.A1⁻¹ * x.A2)
  F3 := x.F3 - x.D * x.A3 * (x.C1 * x.A1)⁻¹
  C := x.A4 - x.A3 * x.A1⁻¹ * x.A2

end ProductReductionStepRawCoordinates

namespace ProductReductionStepChartCoordinates

/-- Determinant-chart domain for the target one-step variables. -/
def detChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    (y : ProductReductionStepChartCoordinates ρ π μ ν K) : Prop :=
  IsUnit y.Ctop.det ∧ IsUnit y.A1.det

/-- Inverse p. 13 triangular coordinate change for one product-reduction step.

Only `A1` and `Ctop` are inverted.  The previous residual block `D` is passive
and is not inverted. -/
def toRaw
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (y : ProductReductionStepChartCoordinates ρ π μ ν K) :
    ProductReductionStepRawCoordinates ρ π μ ν K where
  C1 := y.Ctop * y.A1⁻¹
  D := y.D
  F3 := y.F3 + y.D * y.A3 * y.Ctop⁻¹
  A1 := y.A1
  A2 := -y.A1 * y.F2
  A3 := y.A3
  A4 := y.C - y.A3 * y.F2

end ProductReductionStepChartCoordinates

/-- The forward p. 13 coordinate change preserves determinant-chart
membership. -/
theorem ProductReductionStepRawCoordinates.detChart_toChart
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hx : x.detChart) :
    (x.toChart).detChart := by
  constructor
  · simpa [ProductReductionStepRawCoordinates.toChart, Matrix.det_mul] using
      hx.1.mul hx.2
  · simpa [ProductReductionStepRawCoordinates.toChart] using hx.2

/-- The inverse p. 13 coordinate change preserves determinant-chart
membership. -/
theorem ProductReductionStepChartCoordinates.detChart_toRaw
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (y : ProductReductionStepChartCoordinates ρ π μ ν K)
    (hy : y.detChart) :
    (y.toRaw).detChart := by
  constructor
  · have hA1inv : IsUnit (y.A1⁻¹).det :=
      y.A1.isUnit_nonsing_inv_det hy.2
    simpa [ProductReductionStepChartCoordinates.toRaw, Matrix.det_mul] using
      hy.1.mul hA1inv
  · simpa [ProductReductionStepChartCoordinates.toRaw] using hy.2

/-- Forward followed by inverse recovers the raw one-step coordinates on the
`A1` determinant-unit locus.

This is only the record-level formal inverse calculation.  It does not assert
that the raw point lies in the source determinant chart. -/
theorem productReductionStepCoordinate_left_inverse_of_isUnit_A1
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hA1 : IsUnit x.A1.det) :
    (ProductReductionStepRawCoordinates.toChart x).toRaw = x := by
  cases x with
  | mk C1 D F3 A1 A2 A3 A4 =>
      suffices hneg : - -A2 = A2 by
        simpa [ProductReductionStepRawCoordinates.toChart,
          ProductReductionStepChartCoordinates.toRaw,
          Matrix.mul_nonsing_inv_cancel_left, hA1, Matrix.mul_assoc,
          sub_eq_add_neg] using hneg
      exact neg_neg A2

/-- Forward followed by inverse recovers the raw one-step coordinates.

This is stated on the raw determinant chart, where `C1`, `A1`, and hence
`C1 * A1` are determinant units.  The algebraic cancellation in the proof uses
only the `A1` component; the `C1` component records the source chart needed to
treat `(C1 * A1)^{-1}` as a regular expression.  No inverse of the passive
residual block `D` is used. -/
theorem productReductionStepCoordinate_left_inverse
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hx : x.detChart) :
    (ProductReductionStepRawCoordinates.toChart x).toRaw = x :=
  productReductionStepCoordinate_left_inverse_of_isUnit_A1 x hx.2

/-- Inverse followed by forward recovers the target one-step coordinates on
the `A1` determinant-unit locus.

This is only the record-level formal inverse calculation.  It does not assert
that the chart point lies in the target determinant chart. -/
theorem productReductionStepCoordinate_right_inverse_of_isUnit_A1
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (y : ProductReductionStepChartCoordinates ρ π μ ν K)
    (hA1 : IsUnit y.A1.det) :
    (ProductReductionStepChartCoordinates.toRaw y).toChart = y := by
  cases y with
  | mk Ctop D A1 A3 F2 F3 C =>
      suffices hneg : - -F2 = F2 by
        simpa [ProductReductionStepRawCoordinates.toChart,
          ProductReductionStepChartCoordinates.toRaw, hA1, Matrix.mul_assoc,
          sub_eq_add_neg] using hneg
      exact neg_neg F2

/-- Inverse followed by forward recovers the target one-step coordinates.

The statement includes the determinant-unit condition for `Ctop`, matching the
source chart where `Ctop^{-1}` is a regular expression.  The algebraic
cancellations in this finite inverse check use only the `A1` chart condition. -/
theorem productReductionStepCoordinate_right_inverse
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype μ]
    [DecidableEq μ] [Fintype ν]
    (y : ProductReductionStepChartCoordinates ρ π μ ν K)
    (hA1 : IsUnit y.A1.det) (_hCtop : IsUnit y.Ctop.det) :
    (ProductReductionStepChartCoordinates.toRaw y).toChart = y :=
  productReductionStepCoordinate_right_inverse_of_isUnit_A1 y hA1

/-- The p. 13 one-step coordinate change turns a prior triangular product
identity into the next block-diagonal product identity.

The hypothesis `hT` records the already-accumulated lower triangular
multiplier.  The new variables are `x.toChart`, and the lower-right block is
`D * C`, with no inverse of `D`. -/
theorem productReductionStepCoordinate_triangularBlockProduct
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [DecidableEq π] [Fintype μ] [DecidableEq μ] [Fintype ν]
    [DecidableEq ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hx : x.detChart)
    (T : Matrix (ρ ⊕ π) (ρ ⊕ ν) K)
    (hT :
      fromBlocks (1 : Matrix ρ ρ K) 0 x.F3 (1 : Matrix π π K) * T =
        fromBlocks x.C1 0 0 x.D * fromBlocks x.A1 x.A2 x.A3 x.A4) :
    let y : ProductReductionStepChartCoordinates ρ π μ ν K := x.toChart
    fromBlocks (1 : Matrix ρ ρ K) 0 y.F3 (1 : Matrix π π K) * T *
        fromBlocks (1 : Matrix ρ ρ K) y.F2 0 (1 : Matrix ν ν K) =
      fromBlocks y.Ctop 0 0 (y.D * y.C) := by
  cases x with
  | mk C1 D F3old A1 A2 A3 A4 =>
      let X : Matrix π ρ K := D * A3 * (C1 * A1)⁻¹
      have hlower :
          fromBlocks (1 : Matrix ρ ρ K) 0 (F3old - X)
              (1 : Matrix π π K) =
            fromBlocks (1 : Matrix ρ ρ K) 0 (-X) (1 : Matrix π π K) *
              fromBlocks (1 : Matrix ρ ρ K) 0 F3old (1 : Matrix π π K) := by
        rw [lowerUnitriangular_mul_fromBlocks_one_zero_indexed]
        simp [X, sub_eq_add_neg, add_comm]
      have hstep :=
        productReduction_chartLocalInductionStep_fromBlocks_indexed
          (C1 := C1) (D := D) (A1 := A1) (A2 := A2) (A3 := A3) (A4 := A4)
          hx.1 hx.2
      dsimp [ProductReductionStepRawCoordinates.toChart]
      calc
        fromBlocks (1 : Matrix ρ ρ K) 0 (F3old - X) (1 : Matrix π π K) * T *
            fromBlocks (1 : Matrix ρ ρ K) (-(A1⁻¹ * A2)) 0 (1 : Matrix ν ν K)
            =
          (fromBlocks (1 : Matrix ρ ρ K) 0 (-X) (1 : Matrix π π K) *
              fromBlocks (1 : Matrix ρ ρ K) 0 F3old (1 : Matrix π π K)) * T *
            fromBlocks (1 : Matrix ρ ρ K) (-(A1⁻¹ * A2)) 0 (1 : Matrix ν ν K) := by
            rw [hlower]
        _ =
          fromBlocks (1 : Matrix ρ ρ K) 0 (-X) (1 : Matrix π π K) *
              (fromBlocks (1 : Matrix ρ ρ K) 0 F3old (1 : Matrix π π K) * T) *
            fromBlocks (1 : Matrix ρ ρ K) (-(A1⁻¹ * A2)) 0 (1 : Matrix ν ν K) := by
            simp [Matrix.mul_assoc]
        _ =
          fromBlocks (1 : Matrix ρ ρ K) 0 (-X) (1 : Matrix π π K) *
              (fromBlocks C1 0 0 D * fromBlocks A1 A2 A3 A4) *
            fromBlocks (1 : Matrix ρ ρ K) (-(A1⁻¹ * A2)) 0 (1 : Matrix ν ν K) := by
            rw [hT]
        _ = fromBlocks (C1 * A1) 0 0 (D * (A4 - A3 * A1⁻¹ * A2)) := by
            simpa [X] using hstep

/-- The p. 13 one-step coordinate change gives the displayed signed
product-difference block.

The lower-right correction is `F3 * F2`, matching the block dimensions and the
source calculation. -/
theorem productReductionStepCoordinate_productDifference
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π]
    [DecidableEq π] [Fintype μ] [DecidableEq μ] [Fintype ν]
    [DecidableEq ν]
    (x : ProductReductionStepRawCoordinates ρ π μ ν K)
    (hx : x.detChart)
    (T : Matrix (ρ ⊕ π) (ρ ⊕ ν) K)
    (hT :
      fromBlocks (1 : Matrix ρ ρ K) 0 x.F3 (1 : Matrix π π K) * T =
        fromBlocks x.C1 0 0 x.D * fromBlocks x.A1 x.A2 x.A3 x.A4) :
    let y : ProductReductionStepChartCoordinates ρ π μ ν K := x.toChart
    fromBlocks (1 : Matrix ρ ρ K) 0 y.F3 (1 : Matrix π π K) *
        (T - fromBlocks (1 : Matrix ρ ρ K) 0
          (0 : Matrix π ρ K) (0 : Matrix π ν K)) *
        fromBlocks (1 : Matrix ρ ρ K) y.F2 0 (1 : Matrix ν ν K) =
      fromBlocks (y.Ctop - 1) (-y.F2) (-y.F3) (y.D * y.C - y.F3 * y.F2) := by
  let y : ProductReductionStepChartCoordinates ρ π μ ν K := x.toChart
  have htri :
      fromBlocks (1 : Matrix ρ ρ K) 0 y.F3 (1 : Matrix π π K) * T *
          fromBlocks (1 : Matrix ρ ρ K) y.F2 0 (1 : Matrix ν ν K) =
        fromBlocks y.Ctop 0 0 (y.D * y.C) := by
    simpa [y] using
      productReductionStepCoordinate_triangularBlockProduct
        (x := x) hx T hT
  simpa [y] using
    triangularBlockProductDifference_fromBlocks_indexed
      (F2 := y.F2) (F3 := y.F3) (Ctop := y.Ctop) (D := y.D * y.C)
      (T := T) htri

/-- One suffix step for chart-local product reduction with a supplied transformed edge. -/
theorem productReduction_chartLocal_suffixStep_fromBlocks_indexed
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype π] [DecidableEq π]
    [Fintype μ] [Fintype ν] [DecidableEq ν]
    (Ptail : Matrix (ρ ⊕ π) (ρ ⊕ μ) K)
    (E M : Matrix (ρ ⊕ μ) (ρ ⊕ ν) K)
    (Lprev : Matrix (ρ ⊕ π) (ρ ⊕ π) K)
    (Rprev : Matrix (ρ ⊕ μ) (ρ ⊕ μ) K)
    (Ctop : Matrix ρ ρ K) (Dprev : Matrix π μ K)
    (hPtail : Lprev * Ptail * Rprev = fromBlocks Ctop 0 0 Dprev)
    (hE : E = Rprev * M)
    (hCtop : IsUnit Ctop.det) (hM : identityCornerDetChart M) :
    let Lstep : Matrix (ρ ⊕ π) (ρ ⊕ π) K :=
      fromBlocks (1 : Matrix ρ ρ K) 0
        (-(Dprev * lowerLeftBlock M * (Ctop * topLeftCorner M)⁻¹)) 1
    let Rstep : Matrix (ρ ⊕ ν) (ρ ⊕ ν) K :=
      fromBlocks (1 : Matrix ρ ρ K) (-((topLeftCorner M)⁻¹ * upperRightBlock M)) 0 1
    Lstep * Lprev * (Ptail * E) * Rstep =
      fromBlocks (Ctop * topLeftCorner M) 0 0 (Dprev * schurResidualBlock M) := by
  dsimp
  have hblocks :
      fromBlocks (topLeftCorner M) (upperRightBlock M) (lowerLeftBlock M)
        (lowerRightBlock M) = M :=
    fromBlocks_corners M
  have hstep := productReduction_chartLocalInductionStep_fromBlocks_indexed
    Ctop Dprev (topLeftCorner M) (upperRightBlock M) (lowerLeftBlock M)
    (lowerRightBlock M) hCtop hM
  calc
    fromBlocks (1 : Matrix ρ ρ K) 0
          (-(Dprev * lowerLeftBlock M * (Ctop * topLeftCorner M)⁻¹)) 1 *
        Lprev * (Ptail * E) *
          fromBlocks (1 : Matrix ρ ρ K) (-((topLeftCorner M)⁻¹ * upperRightBlock M)) 0 1
        =
      fromBlocks (1 : Matrix ρ ρ K) 0
          (-(Dprev * lowerLeftBlock M * (Ctop * topLeftCorner M)⁻¹)) 1 *
        ((Lprev * Ptail * Rprev) * M) *
          fromBlocks (1 : Matrix ρ ρ K) (-((topLeftCorner M)⁻¹ * upperRightBlock M)) 0 1 := by
        rw [hE]
        simp only [Matrix.mul_assoc]
    _ =
      fromBlocks (1 : Matrix ρ ρ K) 0
          (-(Dprev * lowerLeftBlock M * (Ctop * topLeftCorner M)⁻¹)) 1 *
        (fromBlocks Ctop 0 0 Dprev * M) *
          fromBlocks (1 : Matrix ρ ρ K) (-((topLeftCorner M)⁻¹ * upperRightBlock M)) 0 1 := by
        rw [hPtail]
    _ =
      fromBlocks (1 : Matrix ρ ρ K) 0
          (-(Dprev * lowerLeftBlock M * (Ctop * topLeftCorner M)⁻¹)) 1 *
        (fromBlocks Ctop 0 0 Dprev *
          fromBlocks (topLeftCorner M) (upperRightBlock M) (lowerLeftBlock M)
            (lowerRightBlock M)) *
          fromBlocks (1 : Matrix ρ ρ K) (-((topLeftCorner M)⁻¹ * upperRightBlock M)) 0 1 := by
        rw [hblocks]
    _ = fromBlocks (Ctop * topLeftCorner M) 0 0
          (Dprev * schurResidualBlock M) := by
        simpa [schurResidualBlock] using hstep

namespace ChartLocalSuffixState

/-- The block-diagonal invariant carried by a deterministic chart-local suffix state. -/
def BlockDiagonal
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    {j i : Fin (N + 1)}
    (S : ChartLocalSuffixState ρ κ K j i)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hij : i ≤ j) : Prop :=
  IsUnit S.L.det ∧ IsUnit S.Ctop.det ∧
    S.L * P i j hij *
        fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0 (1 : Matrix (κ i) (κ i) K) =
      fromBlocks S.Ctop 0 0 S.D

/-- The next transformed edge determined by the current accumulated right block. -/
def transformedEdge
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ) :
    Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K :=
  fromBlocks (1 : Matrix ρ ρ K) S.B 0 (1 : Matrix (κ p.succ) (κ p.succ) K) *
    E p

/-- Raw right-endpoint matrix pattern for Aoyagi's p. 13 product coordinates.

After the terminal suffix state, its transformed edge has block shape
`[I, 0; -F3, C]`. -/
def productCoordinateRightEndpointMatrix
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    (F3 : Matrix μ ρ K) (C : Matrix μ ν K) :
    Matrix (ρ ⊕ μ) (ρ ⊕ ν) K :=
  fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) C

/-- Raw middle-edge matrix pattern for Aoyagi's p. 13 product coordinates.

When the current suffix state has `B = 0`, its transformed edge has block shape
`[I, 0; 0, C]`. -/
def productCoordinateMiddleMatrix
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    (C : Matrix μ ν K) : Matrix (ρ ⊕ μ) (ρ ⊕ ν) K :=
  fromBlocks (1 : Matrix ρ ρ K) 0 (0 : Matrix μ ρ K) C

/-- Raw left-endpoint matrix pattern for Aoyagi's p. 13 product coordinates.

When the current suffix state has `B = 0`, its transformed edge has block shape
`[Ctop, -Ctop F2; 0, C0]`. -/
def productCoordinateLeftEndpointMatrix
    {ρ μ ν : Type*} [Fintype ρ]
    (F2 : Matrix ρ ν K) (Ctop : Matrix ρ ρ K) (C0 : Matrix μ ν K) :
    Matrix (ρ ⊕ μ) (ρ ⊕ ν) K :=
  fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix μ ρ K) C0

/-- Raw single-edge matrix pattern for Aoyagi's p. 13 product coordinates.

At the terminal suffix state its Schur residual is `C0`, while the regular
fields read as `Ctop - I`, `F2`, and `F3`. -/
def productCoordinateSingleEdgeMatrix
    {ρ μ ν : Type*} [Fintype ρ]
    (F2 : Matrix ρ ν K) (F3 : Matrix μ ρ K)
    (Ctop : Matrix ρ ρ K) (C0 : Matrix μ ν K) :
    Matrix (ρ ⊕ μ) (ρ ⊕ ν) K :=
  fromBlocks Ctop (-(Ctop * F2)) (-(F3 * Ctop)) (C0 + F3 * Ctop * F2)

section ProductCoordinateRank

variable {K : Type*} [Field K]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The right-endpoint p.13 product-coordinate matrix has rank equal to the
regular corner size plus the rank of its residual block. -/
theorem rank_productCoordinateRightEndpointMatrix
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    [Fintype μ] [DecidableEq μ] [Fintype ν]
    (F3 : Matrix μ ρ K) (C : Matrix μ ν K) :
    (productCoordinateRightEndpointMatrix F3 C).rank =
      Fintype.card ρ + C.rank := by
  let L : Matrix (ρ ⊕ μ) (ρ ⊕ μ) K :=
    fromBlocks (1 : Matrix ρ ρ K) 0 F3 (1 : Matrix μ μ K)
  have hLdet : IsUnit L.det := by
    exact (Matrix.isUnit_iff_isUnit_det (A := L)).mp
      ((Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩)
  calc
    (productCoordinateRightEndpointMatrix F3 C).rank =
        (L * productCoordinateRightEndpointMatrix F3 C).rank := by
      exact (Matrix.rank_mul_eq_right_of_isUnit_det L
        (productCoordinateRightEndpointMatrix F3 C) hLdet).symm
    _ = (fromBlocks (1 : Matrix ρ ρ K) 0 (0 : Matrix μ ρ K) C).rank := by
      have hmul :
          L * productCoordinateRightEndpointMatrix F3 C =
            fromBlocks (1 : Matrix ρ ρ K) 0 (0 : Matrix μ ρ K) C := by
        change
          fromBlocks (1 : Matrix ρ ρ K) 0 F3 (1 : Matrix μ μ K) *
              fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) C =
            fromBlocks (1 : Matrix ρ ρ K) 0 (0 : Matrix μ ρ K) C
        rw [fromBlocks_multiply]
        simp
      rw [hmul]
    _ = (1 : Matrix ρ ρ K).rank + C.rank := by
      exact rank_fromBlocks_zero_zero (1 : Matrix ρ ρ K) C
    _ = Fintype.card ρ + C.rank := by
      rw [Matrix.rank_one]

/-- The middle p.13 product-coordinate matrix has rank equal to the regular
corner size plus the rank of its residual block. -/
theorem rank_productCoordinateMiddleMatrix
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ν]
    (C : Matrix μ ν K) :
    (productCoordinateMiddleMatrix (ρ := ρ) C).rank =
      Fintype.card ρ + C.rank := by
  calc
    (productCoordinateMiddleMatrix (ρ := ρ) C).rank =
        (fromBlocks (1 : Matrix ρ ρ K) 0 (0 : Matrix μ ρ K) C).rank := by
      rfl
    _ = (1 : Matrix ρ ρ K).rank + C.rank := by
      exact rank_fromBlocks_zero_zero (1 : Matrix ρ ρ K) C
    _ = Fintype.card ρ + C.rank := by
      rw [Matrix.rank_one]

set_option linter.unusedDecidableInType false in
/-- The left-endpoint p.13 product-coordinate matrix has rank equal to the
regular corner size plus the rank of its residual block, provided the displayed
`Ctop` block is in the determinant chart. -/
theorem rank_productCoordinateLeftEndpointMatrix
    {ρ μ ν : Type*} [Fintype ρ] [DecidableEq ρ]
    [Fintype ν] [DecidableEq ν]
    (F2 : Matrix ρ ν K) (Ctop : Matrix ρ ρ K) (C0 : Matrix μ ν K)
    (hCtop : IsUnit Ctop.det) :
    (productCoordinateLeftEndpointMatrix F2 Ctop C0).rank =
      Fintype.card ρ + C0.rank := by
  let R : Matrix (ρ ⊕ ν) (ρ ⊕ ν) K :=
    fromBlocks (1 : Matrix ρ ρ K) F2 0 (1 : Matrix ν ν K)
  have hRdet : IsUnit R.det := by
    exact (Matrix.isUnit_iff_isUnit_det (A := R)).mp
      ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
  calc
    (productCoordinateLeftEndpointMatrix F2 Ctop C0).rank =
        (productCoordinateLeftEndpointMatrix F2 Ctop C0 * R).rank := by
      exact (Matrix.rank_mul_eq_left_of_isUnit_det R
        (productCoordinateLeftEndpointMatrix F2 Ctop C0) hRdet).symm
    _ = (fromBlocks Ctop 0 (0 : Matrix μ ρ K) C0).rank := by
      have hmul :
          productCoordinateLeftEndpointMatrix F2 Ctop C0 * R =
            fromBlocks Ctop 0 (0 : Matrix μ ρ K) C0 := by
        change
          fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix μ ρ K) C0 *
              fromBlocks (1 : Matrix ρ ρ K) F2 0 (1 : Matrix ν ν K) =
            fromBlocks Ctop 0 (0 : Matrix μ ρ K) C0
        rw [fromBlocks_multiply]
        simp
      rw [hmul]
    _ = Ctop.rank + C0.rank := by
      exact rank_fromBlocks_zero_zero Ctop C0
    _ = Fintype.card ρ + C0.rank := by
      rw [Matrix.rank_of_isUnit Ctop ((Matrix.isUnit_iff_isUnit_det (A := Ctop)).mpr hCtop)]

end ProductCoordinateRank

/-- The deterministic suffix-state update hidden in the chart-local induction proof. -/
def step
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ) :
    ChartLocalSuffixState ρ κ K j p.castSucc :=
  let M := transformedEdge E p S
  { L := fromBlocks (1 : Matrix ρ ρ K) 0
        (-(S.D * lowerLeftBlock M * (S.Ctop * topLeftCorner M)⁻¹)) 1 * S.L
    B := (topLeftCorner M)⁻¹ * upperRightBlock M
    Ctop := S.Ctop * topLeftCorner M
    D := S.D * schurResidualBlock M }

/-- A step from a terminal-field suffix state with transformed edge
`[I, 0; -F3, C]` creates the
right-endpoint `F3` field and starts the residual product with `C`. -/
theorem step_finalF3_fromBlocks
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K p.succ p.succ)
    (F3 : Matrix (κ p.succ) ρ K)
    (C : Matrix (κ p.succ) (κ p.castSucc) K)
    (hM :
      transformedEdge E p S =
        fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) C) :
    S.Ctop = 1 →
    S.D = 1 →
    S.L = 1 →
    let S' := step E p S
    S'.B = 0 ∧ S'.Ctop = 1 ∧ S'.D = C ∧
      S'.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3
        (1 : Matrix (κ p.succ) (κ p.succ) K) := by
  intro hCtop hD hL
  suffices - -F3 = F3 by
    simpa [step, hM, hCtop, hD, hL, schurResidualBlock, sub_eq_add_neg] using this
  exact neg_neg F3

/-- A middle transformed edge `[I, 0; 0, C]` preserves the already-created
regular fields and multiplies the residual product by `C`. -/
theorem step_middleResidualFactor_fromBlocks
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N) (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3 : Matrix (κ j) ρ K)
    (Dprev : Matrix (κ j) (κ p.succ) K)
    (C : Matrix (κ p.succ) (κ p.castSucc) K)
    (hM :
      transformedEdge E p S =
        fromBlocks (1 : Matrix ρ ρ K) 0 (0 : Matrix (κ p.succ) ρ K) C)
    (hCtop : S.Ctop = 1)
    (hD : S.D = Dprev)
    (hL :
      S.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3
        (1 : Matrix (κ j) (κ j) K)) :
    let S' := step E p S
    S'.B = 0 ∧ S'.Ctop = 1 ∧ S'.D = Dprev * C ∧
      S'.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3
        (1 : Matrix (κ j) (κ j) K) := by
  simp [step, hM, hCtop, hD, hL, schurResidualBlock, sub_eq_add_neg]

/-- A left-endpoint transformed edge `[Ctop, -Ctop F2; 0, C0]` creates the
`F2` and `Ctop - I` fields without changing the already-created `F3`. -/
theorem step_leftEndpointF2Ctop_fromBlocks
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N) (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F2 : Matrix ρ (κ p.castSucc) K)
    (F3 : Matrix (κ j) ρ K)
    (Dprev : Matrix (κ j) (κ p.succ) K)
    (Ctop : Matrix ρ ρ K)
    (C0 : Matrix (κ p.succ) (κ p.castSucc) K)
    (hM :
      transformedEdge E p S =
        fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix (κ p.succ) ρ K) C0)
    (hCtop_unit : IsUnit Ctop.det)
    (hS_Ctop : S.Ctop = 1)
    (hD : S.D = Dprev)
    (hL :
      S.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3
        (1 : Matrix (κ j) (κ j) K)) :
    let S' := step E p S
    S'.B = -F2 ∧ S'.Ctop = Ctop ∧ S'.D = Dprev * C0 ∧
      S'.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3
        (1 : Matrix (κ j) (κ j) K) := by
  simp [step, hM, hS_Ctop, hD, hL, schurResidualBlock,
    Matrix.nonsing_inv_mul_cancel_left, hCtop_unit, sub_eq_add_neg]

/-- From a terminal-field suffix state, one transformed edge creates the `F2`,
`F3`, and `Ctop - I` fields while leaving the Schur residual equal to `C0`. -/
theorem step_singleEdgeF2F3Ctop_fromBlocks
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K p.succ p.succ)
    (F2 : Matrix ρ (κ p.castSucc) K)
    (F3 : Matrix (κ p.succ) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C0 : Matrix (κ p.succ) (κ p.castSucc) K)
    (hM :
      transformedEdge E p S =
        fromBlocks Ctop (-(Ctop * F2)) (-(F3 * Ctop)) (C0 + F3 * Ctop * F2))
    (hCtop_unit : IsUnit Ctop.det) :
    S.Ctop = 1 →
    S.D = 1 →
    S.L = 1 →
    let S' := step E p S
    S'.B = -F2 ∧ S'.Ctop = Ctop ∧ S'.D = C0 ∧
      S'.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3
        (1 : Matrix (κ p.succ) (κ p.succ) K) := by
  intro hS_Ctop hD hL
  suffices
      F3 * (Ctop * F2) + - - -(F3 * (Ctop * F2)) = 0 ∧ - -F3 = F3 by
    simpa [step, hM, hS_Ctop, hD, hL, schurResidualBlock,
      Matrix.nonsing_inv_mul_cancel_left, hCtop_unit, Matrix.mul_assoc,
      sub_eq_add_neg, add_assoc] using this
  constructor
  · have htriple :
        - - -(F3 * (Ctop * F2)) = -(F3 * (Ctop * F2)) :=
      neg_neg (-(F3 * (Ctop * F2)))
    rw [htriple]
    exact add_neg_cancel (F3 * (Ctop * F2))
  · exact neg_neg F3

/-- Raw p. 13 coordinates attached to one deterministic suffix-state step. -/
def stepRawCoordinates
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K) :
    ProductReductionStepRawCoordinates ρ (κ j) (κ p.succ) (κ p.castSucc) K :=
  let M := transformedEdge E p S
  { C1 := S.Ctop
    D := S.D
    F3 := F3prev
    A1 := topLeftCorner M
    A2 := upperRightBlock M
    A3 := lowerLeftBlock M
    A4 := lowerRightBlock M }

/-- The suffix-state raw step coordinates lie on the determinant chart whenever
the previous `Ctop` block and the transformed edge top-left block do. -/
theorem stepRawCoordinates_detChart
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K)
    (hCtop : IsUnit S.Ctop.det)
    (hM : identityCornerDetChart (transformedEdge E p S)) :
    (stepRawCoordinates E p S F3prev).detChart := by
  exact ⟨hCtop, by
    simpa [stepRawCoordinates, identityCornerDetChart] using hM⟩

/-- The chart top block of the raw suffix-step coordinates is the next
suffix-state top block. -/
theorem stepRawCoordinates_toChart_Ctop
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K) :
    ((stepRawCoordinates E p S F3prev).toChart).Ctop = (step E p S).Ctop := by
  rfl

/-- The chart right block of the raw suffix-step coordinates is the negative
of the next suffix-state right parameter. -/
theorem stepRawCoordinates_toChart_F2
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K) :
    ((stepRawCoordinates E p S F3prev).toChart).F2 = -(step E p S).B := by
  rfl

/-- The chart residual block of the raw suffix-step coordinates is the Schur
residual block of the transformed edge. -/
theorem stepRawCoordinates_toChart_C
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K) :
    ((stepRawCoordinates E p S F3prev).toChart).C =
      schurResidualBlock (transformedEdge E p S) := by
  rfl

/-- The chart lower-right product of the raw suffix-step coordinates is the
next suffix-state residual block. -/
theorem stepRawCoordinates_toChart_D_mul_C
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K) :
    ((stepRawCoordinates E p S F3prev).toChart).D *
        ((stepRawCoordinates E p S F3prev).toChart).C =
      (step E p S).D := by
  rfl

/-- If the previous suffix-state left multiplier is lower unitriangular with
lower block `F3prev`, then the chart lower block of the raw suffix-step
coordinates is the lower-left block of the next suffix-state left multiplier. -/
theorem stepRawCoordinates_toChart_F3_of_L_eq_lowerUnitriangular
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K)
    (hSL :
      S.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3prev
        (1 : Matrix (κ j) (κ j) K)) :
    ((stepRawCoordinates E p S F3prev).toChart).F3 =
      lowerLeftBlock (step E p S).L := by
  let M : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K := transformedEdge E p S
  let X : Matrix (κ j) ρ K :=
    -(S.D * lowerLeftBlock M * (S.Ctop * topLeftCorner M)⁻¹)
  have hL :
      (step E p S).L =
        fromBlocks (1 : Matrix ρ ρ K) 0 (X + F3prev)
          (1 : Matrix (κ j) (κ j) K) := by
    dsimp [step, M]
    rw [hSL]
    simpa [X, M] using
      lowerUnitriangular_mul_fromBlocks_one_zero_indexed (K := K) X F3prev
  dsimp [ProductReductionStepRawCoordinates.toChart, stepRawCoordinates, M]
  rw [hL]
  ext i j
  simp [lowerLeftBlock, X, M, sub_eq_add_neg, add_comm]

/-- A suffix-state block-diagonal invariant supplies the prior triangular
product hypothesis for the p. 13 raw step coordinates. -/
theorem stepRawCoordinates_priorProduct
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K)
    (hS : S.BlockDiagonal P hpj)
    (hSL :
      S.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3prev
        (1 : Matrix (κ j) (κ j) K)) :
    let x := stepRawCoordinates E p S F3prev
    fromBlocks (1 : Matrix ρ ρ K) 0 x.F3 (1 : Matrix (κ j) (κ j) K) *
        P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
      fromBlocks x.C1 0 0 x.D * fromBlocks x.A1 x.A2 x.A3 x.A4 := by
  let M : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K := transformedEdge E p S
  let Rprev : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.succ) K :=
    fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0 (1 : Matrix (κ p.succ) (κ p.succ) K)
  have hfactor : E p = Rprev * M := by
    calc
      E p = (1 : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.succ) K) * E p := by
        rw [Matrix.one_mul]
      _ =
        (fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0
            (1 : Matrix (κ p.succ) (κ p.succ) K) *
          fromBlocks (1 : Matrix ρ ρ K) S.B 0
            (1 : Matrix (κ p.succ) (κ p.succ) K)) * E p := by
          rw [upperUnitriangular_neg_mul_upperUnitriangular S.B]
      _ = Rprev * M := by
          simp [Rprev, M, transformedEdge, Matrix.mul_assoc]
  have hblocks :
      fromBlocks (topLeftCorner M) (upperRightBlock M) (lowerLeftBlock M)
        (lowerRightBlock M) = M :=
    fromBlocks_corners M
  rcases hS with ⟨_, _, hprev⟩
  dsimp [stepRawCoordinates]
  calc
    fromBlocks (1 : Matrix ρ ρ K) 0 F3prev (1 : Matrix (κ j) (κ j) K) *
        P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
      fromBlocks (1 : Matrix ρ ρ K) 0 F3prev (1 : Matrix (κ j) (κ j) K) *
        (P p.succ j hpj * E p) := by
          rw [hsuccRight]
    _ =
      fromBlocks (1 : Matrix ρ ρ K) 0 F3prev (1 : Matrix (κ j) (κ j) K) *
        P p.succ j hpj * (Rprev * M) := by
          rw [hfactor]
          simp [Matrix.mul_assoc]
    _ =
      (fromBlocks (1 : Matrix ρ ρ K) 0 F3prev (1 : Matrix (κ j) (κ j) K) *
          P p.succ j hpj * Rprev) * M := by
          simp [Matrix.mul_assoc]
    _ = (S.L * P p.succ j hpj * Rprev) * M := by
          rw [← hSL]
    _ = fromBlocks S.Ctop 0 0 S.D * M := by
          rw [hprev]
    _ =
      fromBlocks S.Ctop 0 0 S.D *
        fromBlocks (topLeftCorner M) (upperRightBlock M)
          (lowerLeftBlock M) (lowerRightBlock M) := by
          rw [hblocks]

/-- A suffix-state step, expressed in p. 13 raw coordinates, gives the next
triangular block product. -/
theorem stepRawCoordinates_triangularBlockProduct
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K)
    (hS : S.BlockDiagonal P hpj)
    (hSL :
      S.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3prev
        (1 : Matrix (κ j) (κ j) K))
    (hM : identityCornerDetChart (transformedEdge E p S)) :
    let x := stepRawCoordinates E p S F3prev
    let y : ProductReductionStepChartCoordinates ρ (κ j) (κ p.succ) (κ p.castSucc) K :=
      x.toChart
    fromBlocks (1 : Matrix ρ ρ K) 0 y.F3 (1 : Matrix (κ j) (κ j) K) *
        P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) *
        fromBlocks (1 : Matrix ρ ρ K) y.F2 0
          (1 : Matrix (κ p.castSucc) (κ p.castSucc) K) =
      fromBlocks y.Ctop 0 0 (y.D * y.C) := by
  let x := stepRawCoordinates E p S F3prev
  have hx : x.detChart := by
    exact stepRawCoordinates_detChart E p S F3prev hS.2.1 hM
  have hprior :
      fromBlocks (1 : Matrix ρ ρ K) 0 x.F3 (1 : Matrix (κ j) (κ j) K) *
          P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        fromBlocks x.C1 0 0 x.D * fromBlocks x.A1 x.A2 x.A3 x.A4 := by
    simpa [x] using
      stepRawCoordinates_priorProduct E P hsuccRight p hpj S F3prev hS hSL
  simpa [x] using
    productReductionStepCoordinate_triangularBlockProduct
      (x := x) hx (P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj)) hprior

/-- A suffix-state step, expressed in p. 13 raw coordinates, gives the signed
product-difference block. -/
theorem stepRawCoordinates_productDifference
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3prev : Matrix (κ j) ρ K)
    (hS : S.BlockDiagonal P hpj)
    (hSL :
      S.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3prev
        (1 : Matrix (κ j) (κ j) K))
    (hM : identityCornerDetChart (transformedEdge E p S)) :
    let x := stepRawCoordinates E p S F3prev
    let y : ProductReductionStepChartCoordinates ρ (κ j) (κ p.succ) (κ p.castSucc) K :=
      x.toChart
    fromBlocks (1 : Matrix ρ ρ K) 0 y.F3 (1 : Matrix (κ j) (κ j) K) *
        (P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) -
          fromBlocks (1 : Matrix ρ ρ K) 0
            (0 : Matrix (κ j) ρ K) (0 : Matrix (κ j) (κ p.castSucc) K)) *
        fromBlocks (1 : Matrix ρ ρ K) y.F2 0
          (1 : Matrix (κ p.castSucc) (κ p.castSucc) K) =
      fromBlocks (y.Ctop - 1) (-y.F2) (-y.F3) (y.D * y.C - y.F3 * y.F2) := by
  let x := stepRawCoordinates E p S F3prev
  have hx : x.detChart := by
    exact stepRawCoordinates_detChart E p S F3prev hS.2.1 hM
  have hprior :
      fromBlocks (1 : Matrix ρ ρ K) 0 x.F3 (1 : Matrix (κ j) (κ j) K) *
          P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        fromBlocks x.C1 0 0 x.D * fromBlocks x.A1 x.A2 x.A3 x.A4 := by
    simpa [x] using
      stepRawCoordinates_priorProduct E P hsuccRight p hpj S F3prev hS hSL
  simpa [x] using
    productReductionStepCoordinate_productDifference
      (x := x) hx (P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj)) hprior

/-- The terminal deterministic suffix state at the right endpoint. -/
def terminal
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (j : Fin (N + 1)) : ChartLocalSuffixState ρ κ K j j where
  L := 1
  B := 0
  Ctop := 1
  D := 1

/-- The deterministic suffix state obtained by iterating the one-step update downward. -/
def suffixState
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (j i : Fin (N + 1)) (hij : i ≤ j) : ChartLocalSuffixState ρ κ K j i :=
  Nat.decreasingInduction
    (motive := fun m hmj ↦
      ChartLocalSuffixState ρ κ K j ⟨m, lt_of_le_of_lt hmj j.isLt⟩)
    (fun m hms S ↦
      let p : Fin N :=
        ⟨m, Nat.lt_of_succ_le
          ((Nat.succ_le_of_lt hms).trans (Nat.le_of_lt_succ j.isLt))⟩
      by
        simpa [p] using step E p (by simpa [p] using S))
    (by simpa using terminal (ρ := ρ) (κ := κ) (K := K) j)
    (Fin.val_fin_le.mp hij)

/-- The deterministic suffix state is terminal at the right endpoint. -/
@[simp]
theorem suffixState_self
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (j : Fin (N + 1)) :
    suffixState E j j le_rfl = terminal (ρ := ρ) (κ := κ) (K := K) j := by
  simp [suffixState]

/-- The deterministic suffix state's terminal `D` block is identity. -/
@[simp]
theorem suffixState_D_self
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (j : Fin (N + 1)) :
    (suffixState E j j le_rfl).D = 1 := by
  simp [suffixState_self, terminal]

/-- The terminal deterministic suffix state block-diagonalizes the empty suffix. -/
theorem terminal_blockDiagonal
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hself : ∀ j : Fin (N + 1), P j j le_rfl = 1)
    (j : Fin (N + 1)) :
    (terminal (ρ := ρ) (κ := κ) (K := K) j).BlockDiagonal P le_rfl := by
  refine ⟨?_, ?_, ?_⟩
  · simp [terminal]
  · simp [terminal]
  · simp [terminal, hself j]

/-- The deterministic suffix state unfolds by one downward step. -/
theorem suffixState_castSucc
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j) :
    suffixState E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
      step E p (suffixState E j p.succ hpj) := by
  unfold suffixState
  rw [Nat.decreasingInduction_succ_left]
  · simp
  · exact Fin.val_fin_le.mp hpj

/-- Product-family tail suffix fields for a chain with at least two edges.

Edges `1, ..., last` create the right-endpoint `F3` field and preserve
`B = 0`, `Ctop = 1`, and the lower-unitriangular left multiplier until the
left endpoint is processed separately. -/
theorem suffixState_tail_fields_of_productFamily_transformedEdges
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K)
    (hLast :
      transformedEdge E (Fin.last (N + 1))
          (terminal (ρ := ρ) (κ := κ) (K := K) (Fin.last (N + 2))) =
        fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C (Fin.last (N + 1))))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        transformedEdge E p
            (suffixState E (Fin.last (N + 2)) p.succ p.succ.le_last) =
          fromBlocks (1 : Matrix ρ ρ K) 0
            (0 : Matrix (κ p.succ) ρ K) (C p)) :
    let one : Fin (N + 3) := ⟨1, by omega⟩
    let S := suffixState E (Fin.last (N + 2)) one one.le_last
    S.B = 0 ∧ S.Ctop = 1 ∧
      S.L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ (Fin.last (N + 2))) (κ (Fin.last (N + 2))) K) := by
  let j : Fin (N + 3) := Fin.last (N + 2)
  let motive : (m : ℕ) → m ≤ N + 1 → Prop := fun m hm ↦
    0 < m →
      let p : Fin (N + 2) := ⟨m, Nat.lt_succ_of_le hm⟩
      let S := suffixState E j p.castSucc p.castSucc.le_last
      S.B = 0 ∧ S.Ctop = 1 ∧
        S.L =
          fromBlocks (1 : Matrix ρ ρ K) 0 F3
            (1 : Matrix (κ j) (κ j) K)
  have hbase : motive (N + 1) le_rfl := by
    intro _
    let p : Fin (N + 2) := ⟨N + 1, Nat.lt_succ_of_le le_rfl⟩
    have hstate :
        suffixState E j p.castSucc p.castSucc.le_last =
          step E p (suffixState E j p.succ p.succ.le_last) := by
      simpa [j, p] using
        suffixState_castSucc (K := K) E p p.succ.le_last
    have hp_succ : p.succ = j := by
      ext
      simp [p, j]
    have hterminal :
        suffixState E j p.succ p.succ.le_last =
          terminal (ρ := ρ) (κ := κ) (K := K) j := by
      cases hp_succ
      exact suffixState_self (K := K) E j
    have hstep :=
      step_finalF3_fromBlocks (K := K) E p
        (terminal (ρ := ρ) (κ := κ) (K := K) j) F3 (C p)
        (by simpa [j, p] using hLast)
        rfl rfl rfl
    change
      (suffixState E j p.castSucc p.castSucc.le_last).B = 0 ∧
        (suffixState E j p.castSucc p.castSucc.le_last).Ctop = 1 ∧
          (suffixState E j p.castSucc p.castSucc.le_last).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)
    rw [hstate, hterminal]
    exact And.intro hstep.1 (And.intro hstep.2.1 hstep.2.2.2)
  have hstep : ∀ m (hms : m + 1 ≤ N + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih hmpos
    let p : Fin (N + 2) := ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hms)⟩
    let pnext : Fin (N + 2) := ⟨m + 1, Nat.lt_succ_of_le hms⟩
    have hm_lt_last : m < N + 1 := Nat.lt_of_succ_le hms
    have hstate :
        suffixState E j p.castSucc p.castSucc.le_last =
          step E p (suffixState E j p.succ p.succ.le_last) := by
      simpa [j, p] using
        suffixState_castSucc (K := K) E p p.succ.le_last
    have ih' :
        let S := suffixState E j p.succ p.succ.le_last
        S.B = 0 ∧ S.Ctop = 1 ∧
          S.L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K) := by
      simpa [motive, p, pnext, j] using ih (Nat.succ_pos m)
    have hM :
        transformedEdge E p
            (suffixState E j p.succ p.succ.le_last) =
          fromBlocks (1 : Matrix ρ ρ K) 0
            (0 : Matrix (κ p.succ) ρ K) (C p) := by
      exact hMid p hmpos hm_lt_last
    have hstep_fields :=
      step_middleResidualFactor_fromBlocks (K := K) E p
        (suffixState E j p.succ p.succ.le_last) F3
        (suffixState E j p.succ p.succ.le_last).D (C p)
        hM ih'.2.1 rfl ih'.2.2
    change
      (suffixState E j p.castSucc p.castSucc.le_last).B = 0 ∧
        (suffixState E j p.castSucc p.castSucc.le_last).Ctop = 1 ∧
          (suffixState E j p.castSucc p.castSucc.le_last).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)
    rw [hstate]
    exact
      And.intro hstep_fields.1
        (And.intro hstep_fields.2.1 hstep_fields.2.2.2)
  have hall := Nat.decreasingInduction (motive := motive) hstep hbase (show 1 ≤ N + 1 by omega)
  simpa [motive, j] using hall (show 0 < 1 by omega)

/-- Product-coordinate raw tail suffix fields for a chain with at least two
edges.

This version assumes the raw edge matrices have Aoyagi's p. 13 right and
middle product-coordinate block patterns.  The transformed-edge hypotheses are
proved inside the induction from the already-produced `B = 0` field. -/
theorem suffixState_tail_fields_of_productCoordinateEdges
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K)
    (hLast :
      E (Fin.last (N + 1)) =
        productCoordinateRightEndpointMatrix F3 (C (Fin.last (N + 1))))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        E p = productCoordinateMiddleMatrix (ρ := ρ) (C p)) :
    let one : Fin (N + 3) := ⟨1, by omega⟩
    let S := suffixState E (Fin.last (N + 2)) one one.le_last
    S.B = 0 ∧ S.Ctop = 1 ∧
      S.L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ (Fin.last (N + 2))) (κ (Fin.last (N + 2))) K) := by
  let j : Fin (N + 3) := Fin.last (N + 2)
  let motive : (m : ℕ) → m ≤ N + 1 → Prop := fun m hm ↦
    0 < m →
      let p : Fin (N + 2) := ⟨m, Nat.lt_succ_of_le hm⟩
      let S := suffixState E j p.castSucc p.castSucc.le_last
      S.B = 0 ∧ S.Ctop = 1 ∧
        S.L =
          fromBlocks (1 : Matrix ρ ρ K) 0 F3
            (1 : Matrix (κ j) (κ j) K)
  have hbase : motive (N + 1) le_rfl := by
    intro _
    let p : Fin (N + 2) := ⟨N + 1, Nat.lt_succ_of_le le_rfl⟩
    have hstate :
        suffixState E j p.castSucc p.castSucc.le_last =
          step E p (suffixState E j p.succ p.succ.le_last) := by
      simpa [j, p] using
        suffixState_castSucc (K := K) E p p.succ.le_last
    have hp_succ : p.succ = j := by
      ext
      simp [p, j]
    have hterminal :
        suffixState E j p.succ p.succ.le_last =
          terminal (ρ := ρ) (κ := κ) (K := K) j := by
      cases hp_succ
      exact suffixState_self (K := K) E j
    have hM :
        transformedEdge E p
            (terminal (ρ := ρ) (κ := κ) (K := K) p.succ) =
          fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C p) := by
      have hEp :
          E p = fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C p) := by
        simpa [p, productCoordinateRightEndpointMatrix] using hLast
      simp [transformedEdge, terminal, hEp]
    have hstep :=
      step_finalF3_fromBlocks (K := K) E p
        (terminal (ρ := ρ) (κ := κ) (K := K) j) F3 (C p)
        (by
          cases hp_succ
          simpa [p, j] using hM)
        rfl rfl rfl
    change
      (suffixState E j p.castSucc p.castSucc.le_last).B = 0 ∧
        (suffixState E j p.castSucc p.castSucc.le_last).Ctop = 1 ∧
          (suffixState E j p.castSucc p.castSucc.le_last).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)
    rw [hstate, hterminal]
    exact And.intro hstep.1 (And.intro hstep.2.1 hstep.2.2.2)
  have hstep : ∀ m (hms : m + 1 ≤ N + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih hmpos
    let p : Fin (N + 2) := ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hms)⟩
    let pnext : Fin (N + 2) := ⟨m + 1, Nat.lt_succ_of_le hms⟩
    have hm_lt_last : m < N + 1 := Nat.lt_of_succ_le hms
    have hstate :
        suffixState E j p.castSucc p.castSucc.le_last =
          step E p (suffixState E j p.succ p.succ.le_last) := by
      simpa [j, p] using
        suffixState_castSucc (K := K) E p p.succ.le_last
    have ih' :
        let S := suffixState E j p.succ p.succ.le_last
        S.B = 0 ∧ S.Ctop = 1 ∧
          S.L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K) := by
      simpa [motive, p, pnext, j] using ih (Nat.succ_pos m)
    have hM :
        transformedEdge E p
            (suffixState E j p.succ p.succ.le_last) =
          fromBlocks (1 : Matrix ρ ρ K) 0
            (0 : Matrix (κ p.succ) ρ K) (C p) := by
      simp [transformedEdge, productCoordinateMiddleMatrix,
        hMid p hmpos hm_lt_last, ih'.1]
    have hstep_fields :=
      step_middleResidualFactor_fromBlocks (K := K) E p
        (suffixState E j p.succ p.succ.le_last) F3
        (suffixState E j p.succ p.succ.le_last).D (C p)
        hM ih'.2.1 rfl ih'.2.2
    change
      (suffixState E j p.castSucc p.castSucc.le_last).B = 0 ∧
        (suffixState E j p.castSucc p.castSucc.le_last).Ctop = 1 ∧
          (suffixState E j p.castSucc p.castSucc.le_last).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)
    rw [hstate]
    exact
      And.intro hstep_fields.1
        (And.intro hstep_fields.2.1 hstep_fields.2.2.2)
  have hall := Nat.decreasingInduction (motive := motive) hstep hbase (show 1 ≤ N + 1 by omega)
  simpa [motive, j] using hall (show 0 < 1 by omega)

/-- Product-coordinate raw tail suffix fields at any non-left vertex.

After the right endpoint and the middle product-coordinate edges to its right
have been processed, the suffix state has `B = 0`, `Ctop = 1`, and carries the
right endpoint `F3` in the lower-left block of `L`. -/
theorem suffixState_tail_fields_of_productCoordinateEdges_from
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K)
    (hLast :
      E (Fin.last (N + 1)) =
        productCoordinateRightEndpointMatrix F3 (C (Fin.last (N + 1))))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        E p = productCoordinateMiddleMatrix (ρ := ρ) (C p))
    (p : Fin (N + 2)) (hp : 0 < p.val) :
    let j : Fin (N + 3) := Fin.last (N + 2)
    let S := suffixState E j p.castSucc p.castSucc.le_last
    S.B = 0 ∧ S.Ctop = 1 ∧
      S.L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ j) (κ j) K) := by
  let j : Fin (N + 3) := Fin.last (N + 2)
  let motive : (m : ℕ) → m ≤ N + 1 → Prop := fun m hm ↦
    0 < m →
      let q : Fin (N + 2) := ⟨m, Nat.lt_succ_of_le hm⟩
      let S := suffixState E j q.castSucc q.castSucc.le_last
      S.B = 0 ∧ S.Ctop = 1 ∧
        S.L =
          fromBlocks (1 : Matrix ρ ρ K) 0 F3
            (1 : Matrix (κ j) (κ j) K)
  have hbase : motive (N + 1) le_rfl := by
    intro _
    let q : Fin (N + 2) := ⟨N + 1, Nat.lt_succ_of_le le_rfl⟩
    have hstate :
        suffixState E j q.castSucc q.castSucc.le_last =
          step E q (suffixState E j q.succ q.succ.le_last) := by
      simpa [j, q] using
        suffixState_castSucc (K := K) E q q.succ.le_last
    have hq_succ : q.succ = j := by
      ext
      simp [q, j]
    have hterminal :
        suffixState E j q.succ q.succ.le_last =
          terminal (ρ := ρ) (κ := κ) (K := K) j := by
      cases hq_succ
      exact suffixState_self (K := K) E j
    have hM :
        transformedEdge E q
            (terminal (ρ := ρ) (κ := κ) (K := K) q.succ) =
          fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C q) := by
      have hEq :
          E q = fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C q) := by
        simpa [q, productCoordinateRightEndpointMatrix] using hLast
      simp [transformedEdge, terminal, hEq]
    have hstep :=
      step_finalF3_fromBlocks (K := K) E q
        (terminal (ρ := ρ) (κ := κ) (K := K) j) F3 (C q)
        (by
          cases hq_succ
          simpa [q, j] using hM)
        rfl rfl rfl
    change
      (suffixState E j q.castSucc q.castSucc.le_last).B = 0 ∧
        (suffixState E j q.castSucc q.castSucc.le_last).Ctop = 1 ∧
          (suffixState E j q.castSucc q.castSucc.le_last).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)
    rw [hstate, hterminal]
    exact And.intro hstep.1 (And.intro hstep.2.1 hstep.2.2.2)
  have hstep : ∀ m (hms : m + 1 ≤ N + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih hmpos
    let q : Fin (N + 2) := ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hms)⟩
    let qnext : Fin (N + 2) := ⟨m + 1, Nat.lt_succ_of_le hms⟩
    have hm_lt_last : m < N + 1 := Nat.lt_of_succ_le hms
    have hstate :
        suffixState E j q.castSucc q.castSucc.le_last =
          step E q (suffixState E j q.succ q.succ.le_last) := by
      simpa [j, q] using
        suffixState_castSucc (K := K) E q q.succ.le_last
    have ih' :
        let S := suffixState E j q.succ q.succ.le_last
        S.B = 0 ∧ S.Ctop = 1 ∧
          S.L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K) := by
      simpa [motive, q, qnext, j] using ih (Nat.succ_pos m)
    have hM :
        transformedEdge E q
            (suffixState E j q.succ q.succ.le_last) =
          fromBlocks (1 : Matrix ρ ρ K) 0
            (0 : Matrix (κ q.succ) ρ K) (C q) := by
      simp [transformedEdge, productCoordinateMiddleMatrix,
        hMid q hmpos hm_lt_last, ih'.1]
    have hstep_fields :=
      step_middleResidualFactor_fromBlocks (K := K) E q
        (suffixState E j q.succ q.succ.le_last) F3
        (suffixState E j q.succ q.succ.le_last).D (C q)
        hM ih'.2.1 rfl ih'.2.2
    change
      (suffixState E j q.castSucc q.castSucc.le_last).B = 0 ∧
        (suffixState E j q.castSucc q.castSucc.le_last).Ctop = 1 ∧
          (suffixState E j q.castSucc q.castSucc.le_last).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)
    rw [hstate]
    exact
      And.intro hstep_fields.1
        (And.intro hstep_fields.2.1 hstep_fields.2.2.2)
  have hp_le : p.val ≤ N + 1 := Nat.le_of_lt_succ p.isLt
  have hall := Nat.decreasingInduction (motive := motive) hstep hbase hp_le
  simpa [motive, j] using hall hp

/-- Product-family suffix fields for the single-edge case. -/
theorem suffixState_productFamily_fields_fromBlocks_one
    {ρ : Type*} {κ : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin 1, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (p : Fin 1)
    (F2 : Matrix ρ (κ p.castSucc) K)
    (F3 : Matrix (κ p.succ) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C0 : Matrix (κ p.succ) (κ p.castSucc) K)
    (hM :
      transformedEdge E p (terminal (ρ := ρ) (κ := κ) (K := K) p.succ) =
        fromBlocks Ctop (-(Ctop * F2)) (-(F3 * Ctop)) (C0 + F3 * Ctop * F2))
    (hCtop : IsUnit Ctop.det) :
    let S := suffixState E p.succ p.castSucc (Fin.castSucc_le_succ p)
    S.B = -F2 ∧ S.Ctop = Ctop ∧ S.D = C0 ∧
      S.L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ p.succ) (κ p.succ) K) := by
  have hself :
      suffixState E p.succ p.succ le_rfl =
        terminal (ρ := ρ) (κ := κ) (K := K) p.succ :=
    suffixState_self (K := K) E p.succ
  have hstate :
      suffixState E p.succ p.castSucc (Fin.castSucc_le_succ p) =
        step E p (suffixState E p.succ p.succ le_rfl) := by
    simpa using suffixState_castSucc (K := K) E p le_rfl
  have hstep :=
    step_singleEdgeF2F3Ctop_fromBlocks (K := K) E p
      (terminal (ρ := ρ) (κ := κ) (K := K) p.succ) F2 F3 Ctop C0
      hM hCtop rfl rfl rfl
  rw [hstate, hself]
  exact hstep

/-- Product-coordinate raw suffix fields for the single-edge case. -/
theorem suffixState_productCoordinate_fields_one
    {ρ : Type*} {κ : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin 1, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (p : Fin 1)
    (F2 : Matrix ρ (κ p.castSucc) K)
    (F3 : Matrix (κ p.succ) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C0 : Matrix (κ p.succ) (κ p.castSucc) K)
    (hE : E p = productCoordinateSingleEdgeMatrix F2 F3 Ctop C0)
    (hCtop : IsUnit Ctop.det) :
    let S := suffixState E p.succ p.castSucc (Fin.castSucc_le_succ p)
    S.B = -F2 ∧ S.Ctop = Ctop ∧ S.D = C0 ∧
      S.L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ p.succ) (κ p.succ) K) := by
  have hM :
      transformedEdge E p (terminal (ρ := ρ) (κ := κ) (K := K) p.succ) =
        fromBlocks Ctop (-(Ctop * F2)) (-(F3 * Ctop)) (C0 + F3 * Ctop * F2) := by
    simp [transformedEdge, productCoordinateSingleEdgeMatrix, terminal, hE]
  exact
    suffixState_productFamily_fields_fromBlocks_one
      (K := K) E p F2 F3 Ctop C0 hM hCtop

/-- The Schur residual block of the transformed edge visited by the suffix recursion. -/
def residualBlock
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (j : Fin (N + 1)) (p : Fin N) (hpj : p.succ ≤ j) :
    Matrix (κ p.succ) (κ p.castSucc) K :=
  schurResidualBlock
    (transformedEdge E p (suffixState E j p.succ hpj))

/-- The ordered product of transformed Schur residual blocks visited by the
deterministic suffix recursion.

This is the lower-right block product produced by the chart-local algorithm;
it is not a product of the raw input edge lower-right blocks. -/
def residualProduct
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (j i : Fin (N + 1)) (hij : i ≤ j) :
    Matrix (κ j) (κ i) K :=
  Nat.decreasingInduction
    (motive := fun m hmj ↦
      Matrix (κ j) (κ ⟨m, lt_of_le_of_lt hmj j.isLt⟩) K)
    (fun m hms D ↦
      let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (lt_of_le_of_lt hms j.isLt)⟩
      by
        let D' : Matrix (κ j) (κ p.succ) K := by
          simpa [p] using D
        simpa [p] using
          D' * residualBlock E j p (Fin.val_fin_le.mpr hms))
    (by simpa using (1 : Matrix (κ j) (κ j) K))
    (Fin.val_fin_le.mp hij)

/-- The ordered product of an explicitly supplied family of residual factors.

This is the same decreasing endpoint product as `residualProduct`, but with
the visited Schur residual blocks replaced by a supplied matrix family `C`. -/
def residualFactorProduct
    {N : ℕ} {κ : Fin (N + 1) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (j i : Fin (N + 1)) (hij : i ≤ j) :
    Matrix (κ j) (κ i) K :=
  Nat.decreasingInduction
    (motive := fun m hmj ↦
      Matrix (κ j) (κ ⟨m, lt_of_le_of_lt hmj j.isLt⟩) K)
    (fun m hms D ↦
      let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (lt_of_le_of_lt hms j.isLt)⟩
      by
        let D' : Matrix (κ j) (κ p.succ) K := by
          simpa [p] using D
        simpa [p] using D' * C p)
    (by simpa using (1 : Matrix (κ j) (κ j) K))
    (Fin.val_fin_le.mp hij)

/-- The residual product is identity at the right endpoint. -/
@[simp]
theorem residualProduct_self
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (j : Fin (N + 1)) :
    residualProduct E j j le_rfl = 1 := by
  simp [residualProduct]

/-- The explicit residual-factor product is identity at the right endpoint. -/
@[simp]
theorem residualFactorProduct_self
    {N : ℕ} {κ : Fin (N + 1) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (j : Fin (N + 1)) :
    residualFactorProduct C j j le_rfl = 1 := by
  simp [residualFactorProduct]

/-- The residual product unfolds by multiplying the next transformed Schur
residual block. -/
theorem residualProduct_castSucc
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j) :
    residualProduct E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
      residualProduct E j p.succ hpj * residualBlock E j p hpj := by
  unfold residualProduct
  rw [Nat.decreasingInduction_succ_left]
  · congr 1
  · exact Fin.val_fin_le.mp hpj

/-- The explicit residual-factor product unfolds by multiplying the next
supplied residual factor. -/
theorem residualFactorProduct_castSucc
    {N : ℕ} {κ : Fin (N + 1) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j) :
    residualFactorProduct C j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
      residualFactorProduct C j p.succ hpj * C p := by
  unfold residualFactorProduct
  rw [Nat.decreasingInduction_succ_left]
  · congr 1
  · exact Fin.val_fin_le.mp hpj

/-- The explicit residual-factor product splits through an intermediate
residual index. -/
theorem residualFactorProduct_trans
    {N : ℕ} {κ : Fin (N + 1) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {i q j : Fin (N + 1)} (hiq : i ≤ q) (hqj : q ≤ j) :
    residualFactorProduct C j i (hiq.trans hqj) =
      residualFactorProduct C j q hqj * residualFactorProduct C q i hiq := by
  let motive : (m : ℕ) → m ≤ q.val → Prop := fun m hmq ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmq q.isLt⟩
    residualFactorProduct C j im ((Fin.val_fin_le.mpr hmq).trans hqj) =
      residualFactorProduct C j q hqj *
        residualFactorProduct C q im (Fin.val_fin_le.mpr hmq)
  have hbase : motive q.val le_rfl := by
    dsimp [motive]
    simp
  have hstep : ∀ m (hmq : m + 1 ≤ q.val),
      motive (m + 1) hmq → motive m (Nat.le_of_succ_le hmq) := by
    intro m hmq ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (lt_of_le_of_lt hmq q.isLt)⟩
    have hpq : p.succ ≤ q := Fin.val_fin_le.mpr hmq
    have hpj : p.succ ≤ j := hpq.trans hqj
    have ih' :
        residualFactorProduct C j p.succ hpj =
          residualFactorProduct C j q hqj * residualFactorProduct C q p.succ hpq := by
      simpa [motive, p, hpq, hpj] using ih
    calc
      residualFactorProduct C j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
          residualFactorProduct C j p.succ hpj * C p := by
            rw [residualFactorProduct_castSucc]
      _ =
          (residualFactorProduct C j q hqj *
              residualFactorProduct C q p.succ hpq) * C p := by
            rw [ih']
      _ =
          residualFactorProduct C j q hqj *
            (residualFactorProduct C q p.succ hpq * C p) := by
            rw [Matrix.mul_assoc]
      _ =
          residualFactorProduct C j q hqj *
            residualFactorProduct C q p.castSucc ((Fin.castSucc_le_succ p).trans hpq) := by
            rw [← residualFactorProduct_castSucc]
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase
    (Fin.val_fin_le.mp hiq)
  have hcanon' :
      residualFactorProduct C j i
          (Fin.val_fin_le.mpr ((Fin.val_fin_le.mp hiq).trans (Fin.val_fin_le.mp hqj))) =
        residualFactorProduct C j q hqj *
          residualFactorProduct C q i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hiq)) := by
    simpa [motive] using hcanon
  simpa using hcanon'

/-- The explicit residual-factor product over two edges is the product of the
right factor followed by the left factor.

The two middle endpoint expressions `Fin.castSucc (1 : Fin 2)` and
`Fin.succ (0 : Fin 2)` are propositionally equal but not definitionally the
same type index, so the statement displays both factors at the canonical
middle endpoint `(1 : Fin 3)`. -/
theorem residualFactorProduct_fin_two_eq_mul
    {κ : Fin 3 → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) K) :
    residualFactorProduct C (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
      (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) K from
        by simpa using C (1 : Fin 2)) *
      (show Matrix (κ (1 : Fin 3)) (κ 0) K from
        by simpa using C (0 : Fin 2)) := by
  have hsplit :
      residualFactorProduct C (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)) =
        residualFactorProduct C (Fin.last 2) (1 : Fin 3) (by decide) *
          residualFactorProduct C (1 : Fin 3) 0 (by decide) := by
    simpa using
      (residualFactorProduct_trans (K := K) C
        (i := 0) (q := (1 : Fin 3)) (j := Fin.last 2)
        (by decide) (by decide))
  have hright :
      residualFactorProduct C (Fin.last 2) (1 : Fin 3) (by decide) =
        (show Matrix (κ (Fin.last 2)) (κ (1 : Fin 3)) K from
          by simpa using C (1 : Fin 2)) := by
    change residualFactorProduct C (Fin.last 2) (Fin.castSucc (1 : Fin 2))
      (Fin.val_fin_le.mpr (by simp)) =
      (show Matrix (κ (Fin.last 2)) (κ (Fin.castSucc (1 : Fin 2))) K from
        by simpa using C (1 : Fin 2))
    rw [residualFactorProduct_castSucc (K := K) C
      (j := Fin.last 2) (p := (1 : Fin 2)) (Fin.val_fin_le.mpr (by simp))]
    exact Matrix.one_mul
      (show Matrix (κ (Fin.last 2)) (κ (Fin.castSucc (1 : Fin 2))) K from
        by simpa using C (1 : Fin 2))
  have hleft :
      residualFactorProduct C (1 : Fin 3) 0 (by decide) =
        (show Matrix (κ (1 : Fin 3)) (κ 0) K from
          by simpa using C (0 : Fin 2)) := by
    change residualFactorProduct C (Fin.succ (0 : Fin 2)) (Fin.castSucc (0 : Fin 2))
      (Fin.val_fin_le.mpr (by simp)) =
      (show Matrix (κ (Fin.succ (0 : Fin 2))) (κ (Fin.castSucc (0 : Fin 2))) K from
        by simpa using C (0 : Fin 2))
    rw [residualFactorProduct_castSucc (K := K) C
      (j := Fin.succ (0 : Fin 2)) (p := (0 : Fin 2))
      (Fin.val_fin_le.mpr (by simp))]
    exact Matrix.one_mul
      (show Matrix (κ (Fin.succ (0 : Fin 2))) (κ (Fin.castSucc (0 : Fin 2))) K from
        by simpa using C (0 : Fin 2))
  rw [hsplit, hright, hleft]

/-- A residual-factor product factors through every intermediate residual
index, so its matrix rank is bounded by the cardinality of that intermediate
type. -/
theorem rank_residualFactorProduct_le_card_intermediate
    {N : ℕ} {κ : Fin (N + 1) → Type*}
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] [Nontrivial K]
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {i q j : Fin (N + 1)} (hiq : i ≤ q) (hqj : q ≤ j) :
    (residualFactorProduct C j i (hiq.trans hqj)).rank ≤ Fintype.card (κ q) := by
  rw [residualFactorProduct_trans C hiq hqj]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- Residual products agree when all transformed Schur residual blocks visited
by the two suffix recursions agree. -/
theorem residualProduct_eq_of_residualBlock_eq
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E E' : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {i j : Fin (N + 1)} (hij : i ≤ j)
    (hblock : ∀ (p : Fin N) (hpj : p.succ ≤ j),
      residualBlock E j p hpj = residualBlock E' j p hpj) :
    residualProduct E j i hij = residualProduct E' j i hij := by
  let motive : (m : ℕ) → m ≤ j.val → Prop := fun m hmj ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmj j.isLt⟩
    residualProduct E j im (Fin.val_fin_le.mpr hmj) =
      residualProduct E' j im (Fin.val_fin_le.mpr hmj)
  have hbase : motive j.val le_rfl := by
    dsimp [motive]
    simp
  have hstep : ∀ m (hms : m + 1 ≤ j.val),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (lt_of_le_of_lt hms j.isLt)⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have ih' :
        residualProduct E j p.succ hpj =
          residualProduct E' j p.succ hpj := by
      simpa [motive, p, hpj] using ih
    calc
      residualProduct E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
          residualProduct E j p.succ hpj * residualBlock E j p hpj := by
            rw [residualProduct_castSucc]
      _ = residualProduct E' j p.succ hpj * residualBlock E' j p hpj := by
            rw [ih', hblock p hpj]
      _ = residualProduct E' j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) := by
            rw [residualProduct_castSucc]
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase
    (Fin.val_fin_le.mp hij)
  have hcanon' :
      residualProduct E j i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij)) =
        residualProduct E' j i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij)) := by
    simpa [motive] using hcanon
  simpa using hcanon'

/-- A residual product is the explicit factor product when each suffix Schur
residual block below the endpoint `j` is the corresponding supplied factor. -/
theorem residualProduct_eq_residualFactorProduct_of_residualBlock_eq
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {i j : Fin (N + 1)} (hij : i ≤ j)
    (hblock : ∀ (p : Fin N) (hpj : p.succ ≤ j),
      residualBlock E j p hpj = C p) :
    residualProduct E j i hij = residualFactorProduct C j i hij := by
  let motive : (m : ℕ) → m ≤ j.val → Prop := fun m hmj ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmj j.isLt⟩
    residualProduct E j im (Fin.val_fin_le.mpr hmj) =
      residualFactorProduct C j im (Fin.val_fin_le.mpr hmj)
  have hbase : motive j.val le_rfl := by
    dsimp [motive]
    simp
  have hstep : ∀ m (hms : m + 1 ≤ j.val),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (lt_of_le_of_lt hms j.isLt)⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have ih' :
        residualProduct E j p.succ hpj =
          residualFactorProduct C j p.succ hpj := by
      simpa [motive, p, hpj] using ih
    calc
      residualProduct E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
          residualProduct E j p.succ hpj * residualBlock E j p hpj := by
            rw [residualProduct_castSucc]
      _ = residualFactorProduct C j p.succ hpj * C p := by
            rw [ih', hblock p hpj]
      _ = residualFactorProduct C j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) := by
            rw [← residualFactorProduct_castSucc]
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase
    (Fin.val_fin_le.mp hij)
  have hcanon' :
      residualProduct E j i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij)) =
        residualFactorProduct C j i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij)) := by
    simpa [motive] using hcanon
  simpa using hcanon'

/-- The deterministic suffix-state `D` field unfolds by multiplying the next
visited Schur residual block. -/
theorem suffixState_D_castSucc
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j) :
    (suffixState E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)).D =
      (suffixState E j p.succ hpj).D * residualBlock E j p hpj := by
  rw [suffixState_castSucc]
  rfl

/-- The deterministic suffix-state lower-right block is exactly the ordered
product of transformed Schur residual blocks visited by the recursion. -/
theorem suffixState_D_eq_residualProduct
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {i j : Fin (N + 1)} (hij : i ≤ j) :
    (suffixState E j i hij).D = residualProduct E j i hij := by
  let motive : (m : ℕ) → m ≤ j.val → Prop := fun m hmj ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmj j.isLt⟩
    (suffixState E j im (Fin.val_fin_le.mpr hmj)).D =
      residualProduct E j im (Fin.val_fin_le.mpr hmj)
  have hbase : motive j.val le_rfl := by
    dsimp [motive]
    simp [terminal]
  have hstep : ∀ m (hms : m + 1 ≤ j.val),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (lt_of_le_of_lt hms j.isLt)⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have ih' :
        (suffixState E j p.succ hpj).D = residualProduct E j p.succ hpj := by
      simpa [motive, p, hpj] using ih
    calc
      (suffixState E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj)).D =
          (suffixState E j p.succ hpj).D * residualBlock E j p hpj := by
            rw [suffixState_D_castSucc]
      _ = residualProduct E j p.succ hpj * residualBlock E j p hpj := by
            rw [ih']
      _ = residualProduct E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) := by
            rw [residualProduct_castSucc]
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase
    (Fin.val_fin_le.mp hij)
  have hcanon' :
      (suffixState E j i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij))).D =
        residualProduct E j i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij)) := by
    simpa [motive] using hcanon
  simpa using hcanon'

/-- In the one-edge p. 13 product-coordinate matrix, the raw residual product
is the supplied residual block. -/
theorem residualProduct_productCoordinateSingleEdge_eq
    {ρ : Type*} {κ : Fin 2 → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin 1, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (p : Fin 1)
    (F2 : Matrix ρ (κ p.castSucc) K)
    (F3 : Matrix (κ p.succ) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C0 : Matrix (κ p.succ) (κ p.castSucc) K)
    (hE : E p = productCoordinateSingleEdgeMatrix F2 F3 Ctop C0)
    (hCtop : IsUnit Ctop.det) :
    residualProduct E p.succ p.castSucc (Fin.castSucc_le_succ p) = C0 := by
  let S := suffixState E p.succ p.castSucc (Fin.castSucc_le_succ p)
  have hfields :
      S.B = -F2 ∧ S.Ctop = Ctop ∧ S.D = C0 ∧
        S.L =
          fromBlocks (1 : Matrix ρ ρ K) 0 F3
            (1 : Matrix (κ p.succ) (κ p.succ) K) := by
    simpa [S] using
      suffixState_productCoordinate_fields_one
        (K := K) E p F2 F3 Ctop C0 hE hCtop
  have hD :
      S.D = residualProduct E p.succ p.castSucc (Fin.castSucc_le_succ p) := by
    simpa [S] using
      suffixState_D_eq_residualProduct (K := K) E (Fin.castSucc_le_succ p)
  calc
    residualProduct E p.succ p.castSucc (Fin.castSucc_le_succ p) = S.D := by
      rw [← hD]
    _ = C0 := hfields.2.2.1

/-- Product-family suffix fields for a chain with at least two edges. -/
theorem suffixState_productFamily_fields_fromBlocks_succSucc
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F2 : Matrix ρ (κ 0) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K)
    (hLast :
      transformedEdge E (Fin.last (N + 1))
          (terminal (ρ := ρ) (κ := κ) (K := K) (Fin.last (N + 2))) =
        fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C (Fin.last (N + 1))))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        transformedEdge E p
            (suffixState E (Fin.last (N + 2)) p.succ p.succ.le_last) =
          fromBlocks (1 : Matrix ρ ρ K) 0
            (0 : Matrix (κ p.succ) ρ K) (C p))
    (hLeft :
      let p0 : Fin (N + 2) := 0
      let one : Fin (N + 3) := ⟨1, by omega⟩
      transformedEdge E p0 (suffixState E (Fin.last (N + 2)) one one.le_last) =
        fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix (κ one) ρ K) (C p0))
    (hCtop : IsUnit Ctop.det) :
    let p0 : Fin (N + 2) := 0
    let S := suffixState E (Fin.last (N + 2)) p0.castSucc p0.castSucc.le_last
    S.B = -F2 ∧ S.Ctop = Ctop ∧
      S.D = residualProduct E (Fin.last (N + 2)) p0.castSucc p0.castSucc.le_last ∧
      S.L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ (Fin.last (N + 2))) (κ (Fin.last (N + 2))) K) := by
  let p0 : Fin (N + 2) := 0
  let one : Fin (N + 3) := ⟨1, by omega⟩
  let j : Fin (N + 3) := Fin.last (N + 2)
  have hp0_succ : p0.succ = one := by
    ext
    simp [p0, one]
  have htail :
      let S := suffixState E j p0.succ p0.succ.le_last
      S.B = 0 ∧ S.Ctop = 1 ∧
        S.L =
          fromBlocks (1 : Matrix ρ ρ K) 0 F3
            (1 : Matrix (κ j) (κ j) K) := by
    cases hp0_succ
    simpa [p0, one, j] using
      suffixState_tail_fields_of_productFamily_transformedEdges
        (K := K) E F3 C hLast hMid
  have hM :
      transformedEdge E p0 (suffixState E j p0.succ p0.succ.le_last) =
        fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix (κ p0.succ) ρ K) (C p0) := by
    cases hp0_succ
    simpa [p0, one, j] using hLeft
  have hstate :
      suffixState E j p0.castSucc p0.castSucc.le_last =
        step E p0 (suffixState E j p0.succ p0.succ.le_last) := by
    simpa [p0, j] using
      suffixState_castSucc (K := K) E p0 p0.succ.le_last
  have hDres :
      (suffixState E j p0.castSucc p0.castSucc.le_last).D =
        residualProduct E j p0.castSucc p0.castSucc.le_last := by
    simpa [p0, j] using
      suffixState_D_eq_residualProduct (K := K) E p0.castSucc.le_last
  have hstep :=
    step_leftEndpointF2Ctop_fromBlocks (K := K) E p0
      (suffixState E j p0.succ p0.succ.le_last) F2 F3
      (suffixState E j p0.succ p0.succ.le_last).D Ctop (C p0)
      hM hCtop htail.2.1 rfl htail.2.2
  change
    (suffixState E j p0.castSucc p0.castSucc.le_last).B = -F2 ∧
      (suffixState E j p0.castSucc p0.castSucc.le_last).Ctop = Ctop ∧
        (suffixState E j p0.castSucc p0.castSucc.le_last).D =
          residualProduct E j p0.castSucc p0.castSucc.le_last ∧
          (suffixState E j p0.castSucc p0.castSucc.le_last).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)
  rw [hstate]
  refine ⟨hstep.1, hstep.2.1, ?_, hstep.2.2.2⟩
  rw [← hstate]
  exact hDres

/-- Product-coordinate raw suffix fields for a chain with at least two edges.

This assumes the raw fixed matrices have Aoyagi's p. 13 left, middle, and
right product-coordinate patterns.  It derives the transformed-edge block
shapes internally, so callers do not need to state them as separate
hypotheses. -/
theorem suffixState_productCoordinate_fields_succSucc
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F2 : Matrix ρ (κ 0) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K)
    (hLast :
      E (Fin.last (N + 1)) =
        productCoordinateRightEndpointMatrix F3 (C (Fin.last (N + 1))))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        E p = productCoordinateMiddleMatrix (ρ := ρ) (C p))
    (hLeft :
      let p0 : Fin (N + 2) := 0
      E p0 = productCoordinateLeftEndpointMatrix F2 Ctop (C p0))
    (hCtop : IsUnit Ctop.det) :
    let p0 : Fin (N + 2) := 0
    let S := suffixState E (Fin.last (N + 2)) p0.castSucc p0.castSucc.le_last
    S.B = -F2 ∧ S.Ctop = Ctop ∧
      S.D = residualProduct E (Fin.last (N + 2)) p0.castSucc p0.castSucc.le_last ∧
      S.L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ (Fin.last (N + 2))) (κ (Fin.last (N + 2))) K) := by
  let p0 : Fin (N + 2) := 0
  let one : Fin (N + 3) := ⟨1, by omega⟩
  let j : Fin (N + 3) := Fin.last (N + 2)
  have hp0_succ : p0.succ = one := by
    ext
    simp [p0, one]
  have htail :
      let S := suffixState E j p0.succ p0.succ.le_last
      S.B = 0 ∧ S.Ctop = 1 ∧
        S.L =
          fromBlocks (1 : Matrix ρ ρ K) 0 F3
            (1 : Matrix (κ j) (κ j) K) := by
    cases hp0_succ
    simpa [p0, one, j] using
      suffixState_tail_fields_of_productCoordinateEdges
        (K := K) E F3 C hLast hMid
  have hM :
      transformedEdge E p0 (suffixState E j p0.succ p0.succ.le_last) =
        fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix (κ p0.succ) ρ K) (C p0) := by
    have hB0 : (suffixState E j p0.succ p0.succ.le_last).B = 0 := htail.1
    have hLeft' : E p0 = productCoordinateLeftEndpointMatrix F2 Ctop (C p0) := by
      simpa [p0] using hLeft
    dsimp [transformedEdge]
    rw [hB0, hLeft']
    dsimp [productCoordinateLeftEndpointMatrix]
    rw [fromBlocks_one]
    exact Matrix.one_mul _
  have hstate :
      suffixState E j p0.castSucc p0.castSucc.le_last =
        step E p0 (suffixState E j p0.succ p0.succ.le_last) := by
    simpa [p0, j] using
      suffixState_castSucc (K := K) E p0 p0.succ.le_last
  have hDres :
      (suffixState E j p0.castSucc p0.castSucc.le_last).D =
        residualProduct E j p0.castSucc p0.castSucc.le_last := by
    simpa [p0, j] using
      suffixState_D_eq_residualProduct (K := K) E p0.castSucc.le_last
  have hstep :=
    step_leftEndpointF2Ctop_fromBlocks (K := K) E p0
      (suffixState E j p0.succ p0.succ.le_last) F2 F3
      (suffixState E j p0.succ p0.succ.le_last).D Ctop (C p0)
      hM hCtop htail.2.1 rfl htail.2.2
  change
    (suffixState E j p0.castSucc p0.castSucc.le_last).B = -F2 ∧
      (suffixState E j p0.castSucc p0.castSucc.le_last).Ctop = Ctop ∧
        (suffixState E j p0.castSucc p0.castSucc.le_last).D =
          residualProduct E j p0.castSucc p0.castSucc.le_last ∧
          (suffixState E j p0.castSucc p0.castSucc.le_last).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)
  rw [hstate]
  refine ⟨hstep.1, hstep.2.1, ?_, hstep.2.2.2⟩
  rw [← hstate]
  exact hDres

/-- Raw multi-edge product-coordinate matrices satisfy the recursive
determinant-chart hypotheses whenever the left endpoint `Ctop` is a
determinant unit. -/
theorem recursiveDetCharts_productCoordinateEdges_succSucc
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F2 : Matrix ρ (κ 0) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K)
    (hLast :
      E (Fin.last (N + 1)) =
        productCoordinateRightEndpointMatrix F3 (C (Fin.last (N + 1))))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        E p = productCoordinateMiddleMatrix (ρ := ρ) (C p))
    (hLeft :
      let p0 : Fin (N + 2) := 0
      E p0 = productCoordinateLeftEndpointMatrix F2 Ctop (C p0))
    (hCtop : IsUnit Ctop.det) :
    ∀ p : Fin (N + 2),
      identityCornerDetChart
        (transformedEdge E p
          (suffixState E (Fin.last (N + 2)) p.succ p.succ.le_last)) := by
  intro p
  let j : Fin (N + 3) := Fin.last (N + 2)
  by_cases hlast : p.val = N + 1
  · have hp : p = Fin.last (N + 1) := by
      ext
      simpa using hlast
    subst p
    have hsucc : (Fin.last (N + 1)).succ = j := by
      ext
      simp [j]
    have hterminal :
        suffixState E j (Fin.last (N + 1)).succ
            (Fin.last (N + 1)).succ.le_last =
          terminal (ρ := ρ) (κ := κ) (K := K) j := by
      cases hsucc
      exact suffixState_self (K := K) E j
    have hM :
        transformedEdge E (Fin.last (N + 1))
            (suffixState E j (Fin.last (N + 1)).succ
              (Fin.last (N + 1)).succ.le_last) =
          fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C (Fin.last (N + 1))) := by
      have hE :
          E (Fin.last (N + 1)) =
            fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C (Fin.last (N + 1))) := by
        simpa [productCoordinateRightEndpointMatrix] using hLast
      let q : Fin (N + 2) := Fin.last (N + 1)
      have hMterm :
          transformedEdge E q (terminal (ρ := ρ) (κ := κ) (K := K) q.succ) =
            fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C q) := by
        have hEq : E q = fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C q) := by
          simpa [q] using hE
        simp [transformedEdge, terminal, hEq]
      rw [hterminal]
      cases hsucc
      simpa [q] using hMterm
    rw [hM]
    simp [identityCornerDetChart]
  · by_cases hzero : p.val = 0
    · have hp : p = 0 := by
        ext
        simpa using hzero
      subst p
      let p0 : Fin (N + 2) := 0
      let one : Fin (N + 3) := ⟨1, by omega⟩
      have hp0_succ : p0.succ = one := by
        ext
        simp [p0, one]
      have htail :
          let S := suffixState E j p0.succ p0.succ.le_last
          S.B = 0 ∧ S.Ctop = 1 ∧
            S.L =
              fromBlocks (1 : Matrix ρ ρ K) 0 F3
                (1 : Matrix (κ j) (κ j) K) := by
        cases hp0_succ
        simpa [p0, one, j] using
          suffixState_tail_fields_of_productCoordinateEdges
            (K := K) E F3 C hLast hMid
      have hM :
          transformedEdge E p0 (suffixState E j p0.succ p0.succ.le_last) =
            fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix (κ p0.succ) ρ K) (C p0) := by
        have hB0 : (suffixState E j p0.succ p0.succ.le_last).B = 0 := htail.1
        have hLeft' : E p0 = productCoordinateLeftEndpointMatrix F2 Ctop (C p0) := by
          simpa [p0] using hLeft
        dsimp [transformedEdge]
        rw [hB0, hLeft']
        dsimp [productCoordinateLeftEndpointMatrix]
        rw [fromBlocks_one]
        exact Matrix.one_mul _
      rw [hM]
      simpa [identityCornerDetChart] using hCtop
    · have hpos : 0 < p.val := Nat.pos_of_ne_zero hzero
      have hlt : p.val < N + 1 := by
        have hle : p.val ≤ N + 1 := Nat.le_of_lt_succ p.isLt
        exact Nat.lt_of_le_of_ne hle hlast
      let q : Fin (N + 2) := ⟨p.val + 1, by omega⟩
      have hqpos : 0 < q.val := by
        simp [q]
      have hq_cast : q.castSucc = p.succ := by
        ext
        simp [q]
      have htailq :
          let S := suffixState E j q.castSucc q.castSucc.le_last
          S.B = 0 ∧ S.Ctop = 1 ∧
            S.L =
              fromBlocks (1 : Matrix ρ ρ K) 0 F3
                (1 : Matrix (κ j) (κ j) K) := by
        simpa [j] using
          suffixState_tail_fields_of_productCoordinateEdges_from
            (K := K) E F3 C hLast hMid q hqpos
      have hB0 :
          (suffixState E j p.succ p.succ.le_last).B = 0 := by
        cases hq_cast
        simpa using htailq.1
      have hM :
          transformedEdge E p (suffixState E j p.succ p.succ.le_last) =
            fromBlocks (1 : Matrix ρ ρ K) 0
              (0 : Matrix (κ p.succ) ρ K) (C p) := by
        simp [transformedEdge, productCoordinateMiddleMatrix,
          hMid p hpos hlt, hB0]
      rw [hM]
      simp [identityCornerDetChart]

/-- For raw multi-edge product-coordinate matrices, each transformed Schur
residual block visited by the deterministic suffix recursion is the supplied
residual factor `C p`. -/
theorem residualBlock_productCoordinateEdges_succSucc
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F2 : Matrix ρ (κ 0) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K)
    (hLast :
      E (Fin.last (N + 1)) =
        productCoordinateRightEndpointMatrix F3 (C (Fin.last (N + 1))))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        E p = productCoordinateMiddleMatrix (ρ := ρ) (C p))
    (hLeft :
      let p0 : Fin (N + 2) := 0
      E p0 = productCoordinateLeftEndpointMatrix F2 Ctop (C p0)) :
    ∀ p : Fin (N + 2),
      residualBlock E (Fin.last (N + 2)) p p.succ.le_last = C p := by
  intro p
  let j : Fin (N + 3) := Fin.last (N + 2)
  by_cases hlast : p.val = N + 1
  · have hp : p = Fin.last (N + 1) := by
      ext
      simpa using hlast
    subst p
    have hsucc : (Fin.last (N + 1)).succ = j := by
      ext
      simp [j]
    have hterminal :
        suffixState E j (Fin.last (N + 1)).succ
            (Fin.last (N + 1)).succ.le_last =
          terminal (ρ := ρ) (κ := κ) (K := K) j := by
      cases hsucc
      exact suffixState_self (K := K) E j
    have hM :
        transformedEdge E (Fin.last (N + 1))
            (suffixState E j (Fin.last (N + 1)).succ
              (Fin.last (N + 1)).succ.le_last) =
          fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C (Fin.last (N + 1))) := by
      have hE :
          E (Fin.last (N + 1)) =
            fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C (Fin.last (N + 1))) := by
        simpa [productCoordinateRightEndpointMatrix] using hLast
      let q : Fin (N + 2) := Fin.last (N + 1)
      have hMterm :
          transformedEdge E q (terminal (ρ := ρ) (κ := κ) (K := K) q.succ) =
            fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C q) := by
        have hEq : E q = fromBlocks (1 : Matrix ρ ρ K) 0 (-F3) (C q) := by
          simpa [q] using hE
        simp [transformedEdge, terminal, hEq]
      rw [hterminal]
      cases hsucc
      simpa [q] using hMterm
    change
      schurResidualBlock
          (transformedEdge E (Fin.last (N + 1))
            (suffixState E j (Fin.last (N + 1)).succ
              (Fin.last (N + 1)).succ.le_last)) =
        C (Fin.last (N + 1))
    rw [hM]
    simpa using
      schurResidualBlock_fromBlocks_upperRight_zero
        (K := K) (A := (1 : Matrix ρ ρ K)) (C := -F3)
        (D := C (Fin.last (N + 1)))
  · by_cases hzero : p.val = 0
    · have hp : p = 0 := by
        ext
        simpa using hzero
      subst p
      let p0 : Fin (N + 2) := 0
      let one : Fin (N + 3) := ⟨1, by omega⟩
      have hp0_succ : p0.succ = one := by
        ext
        simp [p0, one]
      have htail :
          let S := suffixState E j p0.succ p0.succ.le_last
          S.B = 0 ∧ S.Ctop = 1 ∧
            S.L =
              fromBlocks (1 : Matrix ρ ρ K) 0 F3
                (1 : Matrix (κ j) (κ j) K) := by
        cases hp0_succ
        simpa [p0, one, j] using
          suffixState_tail_fields_of_productCoordinateEdges
            (K := K) E F3 C hLast hMid
      have hM :
          transformedEdge E p0 (suffixState E j p0.succ p0.succ.le_last) =
            fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix (κ p0.succ) ρ K) (C p0) := by
        have hB0 : (suffixState E j p0.succ p0.succ.le_last).B = 0 := htail.1
        have hLeft' : E p0 = productCoordinateLeftEndpointMatrix F2 Ctop (C p0) := by
          simpa [p0] using hLeft
        dsimp [transformedEdge]
        rw [hB0, hLeft']
        dsimp [productCoordinateLeftEndpointMatrix]
        rw [fromBlocks_one]
        exact Matrix.one_mul _
      change
        schurResidualBlock
            (transformedEdge E p0 (suffixState E j p0.succ p0.succ.le_last)) =
          C p0
      rw [hM]
      simpa using
        schurResidualBlock_fromBlocks_lowerLeft_zero
          (K := K) (A := Ctop) (B := -(Ctop * F2)) (D := C p0)
    · have hpos : 0 < p.val := Nat.pos_of_ne_zero hzero
      have hlt : p.val < N + 1 := by
        have hle : p.val ≤ N + 1 := Nat.le_of_lt_succ p.isLt
        exact Nat.lt_of_le_of_ne hle hlast
      let q : Fin (N + 2) := ⟨p.val + 1, by omega⟩
      have hqpos : 0 < q.val := by
        simp [q]
      have hq_cast : q.castSucc = p.succ := by
        ext
        simp [q]
      have htailq :
          let S := suffixState E j q.castSucc q.castSucc.le_last
          S.B = 0 ∧ S.Ctop = 1 ∧
            S.L =
              fromBlocks (1 : Matrix ρ ρ K) 0 F3
                (1 : Matrix (κ j) (κ j) K) := by
        simpa [j] using
          suffixState_tail_fields_of_productCoordinateEdges_from
            (K := K) E F3 C hLast hMid q hqpos
      have hB0 :
          (suffixState E j p.succ p.succ.le_last).B = 0 := by
        cases hq_cast
        simpa using htailq.1
      have hM :
          transformedEdge E p (suffixState E j p.succ p.succ.le_last) =
            fromBlocks (1 : Matrix ρ ρ K) 0
              (0 : Matrix (κ p.succ) ρ K) (C p) := by
        simp [transformedEdge, productCoordinateMiddleMatrix,
          hMid p hpos hlt, hB0]
      change
        schurResidualBlock
            (transformedEdge E p (suffixState E j p.succ p.succ.le_last)) =
          C p
      rw [hM]
      simpa using
        schurResidualBlock_fromBlocks_lowerLeft_zero
          (K := K) (A := (1 : Matrix ρ ρ K))
          (B := (0 : Matrix ρ (κ p.castSucc) K)) (D := C p)

/-- Raw multi-edge product-coordinate matrices have residual product equal to
the explicit ordered product of the supplied residual factors. -/
theorem residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F2 : Matrix ρ (κ 0) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (Ctop : Matrix ρ ρ K)
    (C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K)
    (hLast :
      E (Fin.last (N + 1)) =
        productCoordinateRightEndpointMatrix F3 (C (Fin.last (N + 1))))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        E p = productCoordinateMiddleMatrix (ρ := ρ) (C p))
    (hLeft :
      let p0 : Fin (N + 2) := 0
      E p0 = productCoordinateLeftEndpointMatrix F2 Ctop (C p0)) :
    residualProduct E (Fin.last (N + 2)) 0 (Fin.zero_le (Fin.last (N + 2))) =
      residualFactorProduct C (Fin.last (N + 2)) 0 (Fin.zero_le (Fin.last (N + 2))) := by
  let j : Fin (N + 3) := Fin.last (N + 2)
  have hblocks_last :
      ∀ p : Fin (N + 2),
        residualBlock E j p p.succ.le_last = C p := by
    intro p
    simpa [j] using
      residualBlock_productCoordinateEdges_succSucc
        (K := K) E F2 F3 Ctop C hLast hMid hLeft p
  have hblocks :
      ∀ (p : Fin (N + 2)) (hpj : p.succ ≤ j),
        residualBlock E j p hpj = C p := by
    intro p hpj
    have hhp : hpj = p.succ.le_last := Subsingleton.elim _ _
    cases hhp
    exact hblocks_last p
  have hprod :=
    residualProduct_eq_residualFactorProduct_of_residualBlock_eq
      (K := K) E C (Fin.zero_le j) hblocks
  simpa [j] using hprod

/-- Raw multi-edge product-coordinate matrices preserve the residual product
when their residual factors are chosen to be the base transformed Schur
residual blocks. -/
theorem residualProduct_productCoordinateEdges_succSucc_eq_base
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 3) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (Ebase E : ∀ p : Fin (N + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (F2 : Matrix ρ (κ 0) K)
    (F3 : Matrix (κ (Fin.last (N + 2))) ρ K)
    (Ctop : Matrix ρ ρ K)
    (hLast :
      E (Fin.last (N + 1)) =
        productCoordinateRightEndpointMatrix F3
          (residualBlock Ebase (Fin.last (N + 2)) (Fin.last (N + 1))
            (Fin.last (N + 1)).succ.le_last))
    (hMid :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        E p =
          productCoordinateMiddleMatrix (ρ := ρ)
            (residualBlock Ebase (Fin.last (N + 2)) p p.succ.le_last))
    (hLeft :
      let p0 : Fin (N + 2) := 0
      E p0 =
        productCoordinateLeftEndpointMatrix F2 Ctop
          (residualBlock Ebase (Fin.last (N + 2)) p0 p0.succ.le_last)) :
    residualProduct E (Fin.last (N + 2)) 0 (Fin.zero_le (Fin.last (N + 2))) =
      residualProduct Ebase (Fin.last (N + 2)) 0 (Fin.zero_le (Fin.last (N + 2))) := by
  let j : Fin (N + 3) := Fin.last (N + 2)
  let C : ∀ p : Fin (N + 2), Matrix (κ p.succ) (κ p.castSucc) K :=
    fun p ↦ residualBlock Ebase j p p.succ.le_last
  have hLastC :
      E (Fin.last (N + 1)) =
        productCoordinateRightEndpointMatrix F3 (C (Fin.last (N + 1))) := by
    simpa [C, j] using hLast
  have hMidC :
      ∀ p : Fin (N + 2), 0 < p.val → p.val < N + 1 →
        E p = productCoordinateMiddleMatrix (ρ := ρ) (C p) := by
    intro p hp0 hplast
    simpa [C, j] using hMid p hp0 hplast
  have hLeftC :
      let p0 : Fin (N + 2) := 0
      E p0 = productCoordinateLeftEndpointMatrix F2 Ctop (C p0) := by
    simpa [C, j] using hLeft
  have hblocks_last :
      ∀ p : Fin (N + 2),
        residualBlock E j p p.succ.le_last =
          residualBlock Ebase j p p.succ.le_last := by
    intro p
    simpa [C, j] using
      residualBlock_productCoordinateEdges_succSucc
        (K := K) E F2 F3 Ctop C hLastC hMidC hLeftC p
  have hblocks :
      ∀ (p : Fin (N + 2)) (hpj : p.succ ≤ j),
        residualBlock E j p hpj = residualBlock Ebase j p hpj := by
    intro p hpj
    have hhp : hpj = p.succ.le_last := Subsingleton.elim _ _
    cases hhp
    exact hblocks_last p
  have hprod :=
    residualProduct_eq_of_residualBlock_eq
      (K := K) E Ebase (Fin.zero_le j) hblocks
  simpa [j] using hprod

/-- One deterministic suffix-state update preserves lower-unitriangularity of `L`. -/
theorem step_L_eq_lowerUnitriangular
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N) (S : ChartLocalSuffixState ρ κ K j p.succ)
    (hS : ∃ F3 : Matrix (κ j) ρ K,
      S.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3 (1 : Matrix (κ j) (κ j) K)) :
    ∃ F3 : Matrix (κ j) ρ K,
      (step E p S).L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3 (1 : Matrix (κ j) (κ j) K) := by
  rcases hS with ⟨F3, hF3⟩
  let M : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K := transformedEdge E p S
  let X : Matrix (κ j) ρ K := -(S.D * lowerLeftBlock M * (S.Ctop * topLeftCorner M)⁻¹)
  refine ⟨X + F3, ?_⟩
  dsimp [step, M]
  rw [hF3]
  simpa [X, M] using
    lowerUnitriangular_mul_fromBlocks_one_zero_indexed (K := K) X F3

/-- The deterministic suffix state's accumulated left multiplier is lower unitriangular. -/
theorem suffixState_L_eq_lowerUnitriangular
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    {i j : Fin (N + 1)} (hij : i ≤ j) :
    ∃ F3 : Matrix (κ j) ρ K,
      (suffixState E j i hij).L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3 (1 : Matrix (κ j) (κ j) K) := by
  let motive : (m : ℕ) → m ≤ j.val → Prop := fun m hmj ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmj j.isLt⟩
    ∃ F3 : Matrix (κ j) ρ K,
      (suffixState E j im (Fin.val_fin_le.mpr hmj)).L =
        fromBlocks (1 : Matrix ρ ρ K) 0 F3 (1 : Matrix (κ j) (κ j) K)
  have hbase : motive j.val le_rfl := by
    dsimp [motive]
    refine ⟨0, ?_⟩
    simp [suffixState_self, terminal]
  have hstep : ∀ m (hms : m + 1 ≤ j.val),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (hms.trans_lt j.isLt)⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have ih' :
        ∃ F3 : Matrix (κ j) ρ K,
          (suffixState E j p.succ hpj).L =
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K) := by
      simpa [motive, p, hpj] using ih
    have hnext := step_L_eq_lowerUnitriangular E p
      (suffixState E j p.succ hpj) ih'
    have hstate :
        suffixState E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
          step E p (suffixState E j p.succ hpj) :=
      suffixState_castSucc E p hpj
    rw [← hstate] at hnext
    simpa [motive, p, hpj] using hnext
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hij)
  have hcanon' :
      ∃ F3 : Matrix (κ j) ρ K,
        (suffixState E j i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij))).L =
          fromBlocks (1 : Matrix ρ ρ K) 0 F3 (1 : Matrix (κ j) (κ j) K) := by
    simpa [motive] using hcanon
  simpa using hcanon'

/-- One deterministic suffix-state update preserves the block-diagonal invariant. -/
theorem step_blockDiagonal
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (hS : S.BlockDiagonal P hpj)
    (hchart : identityCornerDetChart (transformedEdge E p S)) :
    (step E p S).BlockDiagonal P ((Fin.castSucc_le_succ p).trans hpj) := by
  rcases hS with ⟨hL, hCtop, hprev⟩
  let Rprev : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.succ) K :=
    fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0 (1 : Matrix (κ p.succ) (κ p.succ) K)
  let M : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K :=
    transformedEdge E p S
  have hfactor : E p = Rprev * M := by
    calc
      E p = (1 : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.succ) K) * E p := by
        rw [Matrix.one_mul]
      _ =
        (fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0
            (1 : Matrix (κ p.succ) (κ p.succ) K) *
          fromBlocks (1 : Matrix ρ ρ K) S.B 0
            (1 : Matrix (κ p.succ) (κ p.succ) K)) * E p := by
          rw [upperUnitriangular_neg_mul_upperUnitriangular S.B]
      _ = Rprev * M := by
          simp [Rprev, M, transformedEdge, Matrix.mul_assoc]
  have hstep := productReduction_chartLocal_suffixStep_fromBlocks_indexed
    (Ptail := P p.succ j hpj) (E := E p) (M := M) (Lprev := S.L)
    (Rprev := Rprev) (Ctop := S.Ctop) (Dprev := S.D) hprev hfactor hCtop hchart
  have hLstep : IsUnit
      (fromBlocks (1 : Matrix ρ ρ K) 0
        (-(S.D * lowerLeftBlock M * (S.Ctop * topLeftCorner M)⁻¹)) 1).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks (1 : Matrix ρ ρ K) 0
          (-(S.D * lowerLeftBlock M * (S.Ctop * topLeftCorner M)⁻¹)) 1)).mp
      ((Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩)
  refine ⟨?_, ?_, ?_⟩
  · simpa [step, M, Matrix.det_mul] using hLstep.mul hL
  · simpa [step, M, Matrix.det_mul] using hCtop.mul hchart
  · dsimp [BlockDiagonal, step, M]
    rw [hsuccRight p j hpj]
    exact hstep

/-- The deterministic suffix state block-diagonalizes the whole suffix. -/
theorem suffixState_blockDiagonal
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hPproof : ∀ {i j : Fin (N + 1)} (h h' : i ≤ j), P i j h = P i j h')
    (hself : ∀ j : Fin (N + 1), P j j le_rfl = 1)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    {i j : Fin (N + 1)} (hij : i ≤ j)
    (hchart : ∀ (p : Fin N) (hpj : p.succ ≤ j),
      identityCornerDetChart (transformedEdge E p (suffixState E j p.succ hpj))) :
    (suffixState E j i hij).BlockDiagonal P hij := by
  let motive : (m : ℕ) → m ≤ j.val → Prop := fun m hmj ↦
    let im : Fin (N + 1) := ⟨m, lt_of_le_of_lt hmj j.isLt⟩
    (suffixState E j im (Fin.val_fin_le.mpr hmj)).BlockDiagonal P
      (Fin.val_fin_le.mpr hmj)
  have hbase : motive j.val le_rfl := by
    dsimp [motive]
    simpa [suffixState_self] using terminal_blockDiagonal P hself j
  have hstep : ∀ m (hms : m + 1 ≤ j.val),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_lt_succ (hms.trans_lt j.isLt)⟩
    have hpj : p.succ ≤ j := Fin.val_fin_le.mpr hms
    have ih' : (suffixState E j p.succ hpj).BlockDiagonal P hpj := by
      simpa [motive, p, hpj] using ih
    have hnext := step_blockDiagonal E P hsuccRight p hpj
      (suffixState E j p.succ hpj) ih' (hchart p hpj)
    have hstate :
        suffixState E j p.castSucc ((Fin.castSucc_le_succ p).trans hpj) =
          step E p (suffixState E j p.succ hpj) :=
      suffixState_castSucc E p hpj
    rw [← hstate] at hnext
    simpa [motive, p, hpj] using hnext
  have hcanon := Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hij)
  have hcanon' :
      (suffixState E j i (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij))).BlockDiagonal P
        (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij)) := by
    simpa [motive] using hcanon
  simpa [BlockDiagonal, hPproof hij (Fin.val_fin_le.mpr (Fin.val_fin_le.mp hij))] using hcanon'

/-- For the actual recursive suffix state, the p. 13 raw-step coordinates give
the next triangular block product. -/
theorem suffixState_stepRawCoordinates_triangularBlockProduct
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j)
    (hS : (suffixState E j p.succ hpj).BlockDiagonal P hpj)
    (hM : identityCornerDetChart
      (transformedEdge E p (suffixState E j p.succ hpj))) :
    ∃ F3prev : Matrix (κ j) ρ K,
      let S : ChartLocalSuffixState ρ κ K j p.succ := suffixState E j p.succ hpj
      let x := stepRawCoordinates E p S F3prev
      let y : ProductReductionStepChartCoordinates ρ (κ j) (κ p.succ) (κ p.castSucc) K :=
        x.toChart
      fromBlocks (1 : Matrix ρ ρ K) 0 y.F3 (1 : Matrix (κ j) (κ j) K) *
          P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) *
          fromBlocks (1 : Matrix ρ ρ K) y.F2 0
            (1 : Matrix (κ p.castSucc) (κ p.castSucc) K) =
      fromBlocks y.Ctop 0 0 (y.D * y.C) := by
  let S : ChartLocalSuffixState ρ κ K j p.succ := suffixState E j p.succ hpj
  have hS' : S.BlockDiagonal P hpj := by
    simpa [S] using hS
  have hM' : identityCornerDetChart (transformedEdge E p S) := by
    simpa [S] using hM
  rcases suffixState_L_eq_lowerUnitriangular (K := K) E hpj with ⟨F3prev, hSL⟩
  refine ⟨F3prev, ?_⟩
  simpa [S] using
    stepRawCoordinates_triangularBlockProduct
      (E := E) (P := P) hsuccRight p hpj S F3prev hS' hSL hM'

/-- For the actual recursive suffix state, the p. 13 raw-step coordinates give
the signed product-difference block. -/
theorem suffixState_stepRawCoordinates_productDifference
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    {j : Fin (N + 1)} (p : Fin N) (hpj : p.succ ≤ j)
    (hS : (suffixState E j p.succ hpj).BlockDiagonal P hpj)
    (hM : identityCornerDetChart
      (transformedEdge E p (suffixState E j p.succ hpj))) :
    ∃ F3prev : Matrix (κ j) ρ K,
      let S : ChartLocalSuffixState ρ κ K j p.succ := suffixState E j p.succ hpj
      let x := stepRawCoordinates E p S F3prev
      let y : ProductReductionStepChartCoordinates ρ (κ j) (κ p.succ) (κ p.castSucc) K :=
        x.toChart
      fromBlocks (1 : Matrix ρ ρ K) 0 y.F3 (1 : Matrix (κ j) (κ j) K) *
          (P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) -
            fromBlocks (1 : Matrix ρ ρ K) 0
              (0 : Matrix (κ j) ρ K) (0 : Matrix (κ j) (κ p.castSucc) K)) *
          fromBlocks (1 : Matrix ρ ρ K) y.F2 0
            (1 : Matrix (κ p.castSucc) (κ p.castSucc) K) =
        fromBlocks (y.Ctop - 1) (-y.F2) (-y.F3) (y.D * y.C - y.F3 * y.F2) := by
  let S : ChartLocalSuffixState ρ κ K j p.succ := suffixState E j p.succ hpj
  have hS' : S.BlockDiagonal P hpj := by
    simpa [S] using hS
  have hM' : identityCornerDetChart (transformedEdge E p S) := by
    simpa [S] using hM
  rcases suffixState_L_eq_lowerUnitriangular (K := K) E hpj with ⟨F3prev, hSL⟩
  refine ⟨F3prev, ?_⟩
  simpa [S] using
    stepRawCoordinates_productDifference
      (E := E) (P := P) hsuccRight p hpj S F3prev hS' hSL hM'

/-- A deterministic block-diagonal suffix state gives Aoyagi-style triangular multipliers. -/
theorem suffixState_blockDiagonal_exists_triangularBlockDiagonal
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    {i j : Fin (N + 1)} (hij : i ≤ j)
    (hS : (suffixState E j i hij).BlockDiagonal P hij) :
    ∃ F2 : Matrix ρ (κ i) K, ∃ F3 : Matrix (κ j) ρ K,
      ∃ Ctop : Matrix ρ ρ K, ∃ D : Matrix (κ j) (κ i) K,
          IsUnit
            (fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)).det ∧
          IsUnit
            (fromBlocks (1 : Matrix ρ ρ K) F2 0
              (1 : Matrix (κ i) (κ i) K)).det ∧
          IsUnit Ctop.det ∧
          fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K) *
            P i j hij *
            fromBlocks (1 : Matrix ρ ρ K) F2 0
              (1 : Matrix (κ i) (κ i) K) =
          fromBlocks Ctop 0 0 D := by
  let S : ChartLocalSuffixState ρ κ K j i := suffixState E j i hij
  rcases hS with ⟨_, hCtop, hdiag⟩
  rcases suffixState_L_eq_lowerUnitriangular E hij with ⟨F3, hF3⟩
  have hLeft : IsUnit
      (fromBlocks (1 : Matrix ρ ρ K) 0 F3
        (1 : Matrix (κ j) (κ j) K)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ j) (κ j) K))).mp
      ((Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩)
  have hRight : IsUnit
      (fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0
        (1 : Matrix (κ i) (κ i) K)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0
          (1 : Matrix (κ i) (κ i) K))).mp
      ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
  refine ⟨-S.B, F3, S.Ctop, S.D, hLeft, hRight, hCtop, ?_⟩
  simpa [S, hF3] using hdiag

/-- A deterministic block-diagonal suffix state gives triangular multipliers
whose lower-right block is the named transformed residual product. -/
theorem suffixState_blockDiagonal_exists_triangularBlockDiagonal_residualProduct
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    {i j : Fin (N + 1)} (hij : i ≤ j)
    (hS : (suffixState E j i hij).BlockDiagonal P hij) :
    ∃ F2 : Matrix ρ (κ i) K, ∃ F3 : Matrix (κ j) ρ K,
      ∃ Ctop : Matrix ρ ρ K,
          IsUnit
            (fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K)).det ∧
          IsUnit
            (fromBlocks (1 : Matrix ρ ρ K) F2 0
              (1 : Matrix (κ i) (κ i) K)).det ∧
          IsUnit Ctop.det ∧
          fromBlocks (1 : Matrix ρ ρ K) 0 F3
              (1 : Matrix (κ j) (κ j) K) *
            P i j hij *
            fromBlocks (1 : Matrix ρ ρ K) F2 0
              (1 : Matrix (κ i) (κ i) K) =
          fromBlocks Ctop 0 0 (residualProduct E j i hij) := by
  let S : ChartLocalSuffixState ρ κ K j i := suffixState E j i hij
  rcases hS with ⟨_, hCtop, hdiag⟩
  rcases suffixState_L_eq_lowerUnitriangular E hij with ⟨F3, hF3⟩
  have hLeft : IsUnit
      (fromBlocks (1 : Matrix ρ ρ K) 0 F3
        (1 : Matrix (κ j) (κ j) K)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ j) (κ j) K))).mp
      ((Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩)
  have hRight : IsUnit
      (fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0
        (1 : Matrix (κ i) (κ i) K)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
        (A := fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0
          (1 : Matrix (κ i) (κ i) K))).mp
      ((Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩)
  have hD : S.D = residualProduct E j i hij := by
    simpa [S] using suffixState_D_eq_residualProduct (K := K) E hij
  refine ⟨-S.B, F3, S.Ctop, hLeft, hRight, hCtop, ?_⟩
  calc
    fromBlocks (1 : Matrix ρ ρ K) 0 F3
          (1 : Matrix (κ j) (κ j) K) *
        P i j hij *
        fromBlocks (1 : Matrix ρ ρ K) (-S.B) 0
          (1 : Matrix (κ i) (κ i) K) =
        fromBlocks S.Ctop 0 0 S.D := by
          simpa [S, hF3] using hdiag
    _ = fromBlocks S.Ctop 0 0 (residualProduct E j i hij) := by
          rw [hD]

end ChartLocalSuffixState

/-- Abstract suffix-chain block diagonalisation on explicit determinant charts. -/
theorem productReduction_chartLocal_suffixChain_blockDiagonal_indexed
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hPproof : ∀ {i j : Fin (N + 1)} (h h' : i ≤ j), P i j h = P i j h')
    (hself : ∀ j : Fin (N + 1), P j j le_rfl = 1)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    (hchart : ∀ (p : Fin N) (Bprev : Matrix ρ (κ p.succ) K),
      identityCornerDetChart
        (fromBlocks (1 : Matrix ρ ρ K) Bprev 0
          (1 : Matrix (κ p.succ) (κ p.succ) K) * E p)) :
    ∀ i j : Fin (N + 1), ∀ hij : i ≤ j,
      ∃ L : Matrix (ρ ⊕ κ j) (ρ ⊕ κ j) K,
        ∃ B : Matrix ρ (κ i) K,
          ∃ Ctop : Matrix ρ ρ K,
            ∃ D : Matrix (κ j) (κ i) K,
              IsUnit L.det ∧ IsUnit Ctop.det ∧
                L * P i j hij *
                    fromBlocks (1 : Matrix ρ ρ K) (-B) 0
                      (1 : Matrix (κ i) (κ i) K) =
                  fromBlocks Ctop 0 0 D := by
  intro i j hij
  let S : ChartLocalSuffixState ρ κ K j i := ChartLocalSuffixState.suffixState E j i hij
  have hS : S.BlockDiagonal P hij := by
    dsimp [S]
    exact ChartLocalSuffixState.suffixState_blockDiagonal E P hPproof hself hsuccRight hij
      (fun p hpj ↦ by
        simpa [ChartLocalSuffixState.transformedEdge] using
          hchart p (ChartLocalSuffixState.suffixState E j p.succ hpj).B)
  rcases hS with ⟨hL, hCtop, hdiag⟩
  exact ⟨S.L, S.B, S.Ctop, S.D, hL, hCtop, hdiag⟩

/-- Abstract suffix-chain block diagonalisation with Aoyagi-style triangular multipliers. -/
theorem productReduction_chartLocal_suffixChain_triangularBlockDiagonal_indexed
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hPproof : ∀ {i j : Fin (N + 1)} (h h' : i ≤ j), P i j h = P i j h')
    (hself : ∀ j : Fin (N + 1), P j j le_rfl = 1)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    (hchart : ∀ (p : Fin N) (Bprev : Matrix ρ (κ p.succ) K),
      identityCornerDetChart
        (fromBlocks (1 : Matrix ρ ρ K) Bprev 0
          (1 : Matrix (κ p.succ) (κ p.succ) K) * E p)) :
    ∀ i j : Fin (N + 1), ∀ hij : i ≤ j,
      ∃ F2 : Matrix ρ (κ i) K, ∃ F3 : Matrix (κ j) ρ K,
        ∃ Ctop : Matrix ρ ρ K, ∃ D : Matrix (κ j) (κ i) K,
          IsUnit
              (fromBlocks (1 : Matrix ρ ρ K) 0 F3
                (1 : Matrix (κ j) (κ j) K)).det ∧
            IsUnit
              (fromBlocks (1 : Matrix ρ ρ K) F2 0
                (1 : Matrix (κ i) (κ i) K)).det ∧
            IsUnit Ctop.det ∧
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
                (1 : Matrix (κ j) (κ j) K) *
              P i j hij *
              fromBlocks (1 : Matrix ρ ρ K) F2 0
                (1 : Matrix (κ i) (κ i) K) =
            fromBlocks Ctop 0 0 D := by
  intro i j hij
  let S : ChartLocalSuffixState ρ κ K j i := ChartLocalSuffixState.suffixState E j i hij
  have hS : S.BlockDiagonal P hij := by
    dsimp [S]
    exact ChartLocalSuffixState.suffixState_blockDiagonal E P hPproof hself hsuccRight hij
      (fun p hpj ↦ by
        simpa [ChartLocalSuffixState.transformedEdge] using
          hchart p (ChartLocalSuffixState.suffixState E j p.succ hpj).B)
  exact ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal
    E P hij hS

/-- Abstract suffix-chain block diagonalisation with Aoyagi-style triangular
multipliers and a named lower-right product of transformed Schur residuals. -/
theorem productReduction_chartLocal_suffixChain_triangularBlockDiagonal_residualProduct_indexed
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ]
    [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (P : ∀ i j : Fin (N + 1), i ≤ j → Matrix (ρ ⊕ κ j) (ρ ⊕ κ i) K)
    (hPproof : ∀ {i j : Fin (N + 1)} (h h' : i ≤ j), P i j h = P i j h')
    (hself : ∀ j : Fin (N + 1), P j j le_rfl = 1)
    (hsuccRight : ∀ (p : Fin N) (j : Fin (N + 1)) (hpj : p.succ ≤ j),
      P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj) =
        P p.succ j hpj * E p)
    (hchart : ∀ (p : Fin N) (Bprev : Matrix ρ (κ p.succ) K),
      identityCornerDetChart
        (fromBlocks (1 : Matrix ρ ρ K) Bprev 0
          (1 : Matrix (κ p.succ) (κ p.succ) K) * E p)) :
    ∀ i j : Fin (N + 1), ∀ hij : i ≤ j,
      ∃ F2 : Matrix ρ (κ i) K, ∃ F3 : Matrix (κ j) ρ K,
        ∃ Ctop : Matrix ρ ρ K,
          IsUnit
              (fromBlocks (1 : Matrix ρ ρ K) 0 F3
                (1 : Matrix (κ j) (κ j) K)).det ∧
            IsUnit
              (fromBlocks (1 : Matrix ρ ρ K) F2 0
                (1 : Matrix (κ i) (κ i) K)).det ∧
            IsUnit Ctop.det ∧
            fromBlocks (1 : Matrix ρ ρ K) 0 F3
                (1 : Matrix (κ j) (κ j) K) *
              P i j hij *
              fromBlocks (1 : Matrix ρ ρ K) F2 0
                (1 : Matrix (κ i) (κ i) K) =
            fromBlocks Ctop 0 0
              (ChartLocalSuffixState.residualProduct E j i hij) := by
  intro i j hij
  let S : ChartLocalSuffixState ρ κ K j i := ChartLocalSuffixState.suffixState E j i hij
  have hS : S.BlockDiagonal P hij := by
    dsimp [S]
    exact ChartLocalSuffixState.suffixState_blockDiagonal E P hPproof hself hsuccRight hij
      (fun p hpj ↦ by
        simpa [ChartLocalSuffixState.transformedEdge] using
          hchart p (ChartLocalSuffixState.suffixState E j p.succ hpj).B)
  exact
    ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal_residualProduct
      E P hij hS

end InductionStep

section SchurResidualRank

variable {K : Type*} [Field K]

/-- On the determinant chart, the selected Schur residual has rank `rank M - r`. -/
theorem rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart {r p q : ℕ}
    (M : Matrix (Fin r ⊕ Fin p) (Fin r ⊕ Fin q) K)
    (hM : identityCornerDetChart M) :
    (schurResidualBlock M).rank = M.rank - r := by
  let A1 : Matrix (Fin r) (Fin r) K := topLeftCorner M
  let A2 : Matrix (Fin r) (Fin q) K := upperRightBlock M
  let A3 : Matrix (Fin p) (Fin r) K := lowerLeftBlock M
  let A4 : Matrix (Fin p) (Fin q) K := lowerRightBlock M
  have hblocks : fromBlocks A1 A2 A3 A4 = M := by
    simpa [A1, A2, A3, A4] using fromBlocks_corners (K := K) M
  have hrank : (fromBlocks A1 A2 A3 A4).rank = M.rank := by
    rw [hblocks]
  have hschur := rank_schurComplement_eq_sub_rank_fromBlocks A1 A2 A3 A4 hM hrank
  simpa [schurResidualBlock, A1, A2, A3, A4] using hschur

end SchurResidualRank

end Aoyagi
end DLN
end DLNFibre
