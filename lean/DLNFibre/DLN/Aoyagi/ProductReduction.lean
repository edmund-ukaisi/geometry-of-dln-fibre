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

/-- The residual product is identity at the right endpoint. -/
@[simp]
theorem residualProduct_self
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K)
    (j : Fin (N + 1)) :
    residualProduct E j j le_rfl = 1 := by
  simp [residualProduct]

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
