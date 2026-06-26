import DLNFibre.DLN.Aoyagi.ProductReduction

/-!
# Retained-passive product-reduction coordinates

This file records the first finite algebraic spine for the retained-passive
p.13 coordinate construction: fixed-base edge matrices whose deterministic
suffix-state transformed edges are prescribed chart blocks.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi
namespace ChartLocalSuffixState

section RetainedPassive

variable {K : Type*} [CommRing K]
variable {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
variable [Fintype ρ] [DecidableEq ρ]
variable [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]

/-- The retained-passive transformed edge block for one product-reduction step. -/
def retainedPassiveTransformedEdge
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (p : Fin N) : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K :=
  fromBlocks (A1 p) (-(A1 p * F2 p.castSucc)) (A3 p)
    (C p - A3 p * F2 p.castSucc)

/-- Fixed-base edge matrices obtained from retained-passive transformed blocks
by undoing the next suffix state's upper-unitriangular multiplier. -/
def retainedPassiveFixedBaseEdgeMatrix
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (p : Fin N) : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K :=
  fromBlocks (1 : Matrix ρ ρ K) (F2 p.succ) 0
      (1 : Matrix (κ p.succ) (κ p.succ) K) *
    retainedPassiveTransformedEdge A1 F2 A3 C p

/-- If the next suffix-state right field is `-F2_{p+1}`, the fixed-base edge
has the prescribed retained-passive transformed edge. -/
theorem transformedEdge_retainedPassiveFixedBaseEdgeMatrix_of_B_eq
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (hB : S.B = -F2 p.succ) :
    transformedEdge (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C) p S =
      retainedPassiveTransformedEdge A1 F2 A3 C p := by
  dsimp [transformedEdge, retainedPassiveFixedBaseEdgeMatrix]
  rw [hB, ← Matrix.mul_assoc]
  rw [upperUnitriangular_neg_mul_upperUnitriangular (K := K) (F2 p.succ)]
  exact Matrix.one_mul _

/-- One retained-passive step updates the suffix-state right field from
`-F2_{p+1}` to `-F2_p`. -/
theorem step_retainedPassiveFixedBaseEdgeMatrix_B
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (hB : S.B = -F2 p.succ)
    (hA1 : IsUnit (A1 p).det) :
    (step (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C) p S).B =
      -F2 p.castSucc := by
  have hM :=
    transformedEdge_retainedPassiveFixedBaseEdgeMatrix_of_B_eq
      A1 F2 A3 C p S hB
  simp [step, hM, retainedPassiveTransformedEdge,
    Matrix.nonsing_inv_mul_cancel_left, hA1, Matrix.mul_assoc]

/-- One retained-passive step updates the suffix-state top block by multiplying
with the prescribed `A1_p`. -/
theorem step_retainedPassiveFixedBaseEdgeMatrix_Ctop
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (hB : S.B = -F2 p.succ) :
    (step (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C) p S).Ctop =
      S.Ctop * A1 p := by
  have hM :=
    transformedEdge_retainedPassiveFixedBaseEdgeMatrix_of_B_eq
      A1 F2 A3 C p S hB
  simp [step, hM, retainedPassiveTransformedEdge]

omit [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] in
/-- The Schur residual block of a retained-passive transformed edge is the
prescribed residual block `C_p`. -/
theorem schurResidualBlock_retainedPassiveTransformedEdge
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (p : Fin N)
    (hA1 : IsUnit (A1 p).det) :
    schurResidualBlock (retainedPassiveTransformedEdge A1 F2 A3 C p) =
      C p := by
  simp [schurResidualBlock, retainedPassiveTransformedEdge,
    Matrix.nonsing_inv_mul_cancel_left, hA1, Matrix.mul_assoc,
    sub_eq_add_neg, add_assoc]

omit [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] in
/-- The one-step chart readbacks of a retained-passive transformed edge recover
the supplied retained-passive coordinate blocks. -/
theorem retainedPassiveTransformedEdge_readbacks
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (p : Fin N)
    (hA1 : IsUnit (A1 p).det) :
    topLeftCorner (retainedPassiveTransformedEdge A1 F2 A3 C p) = A1 p ∧
      upperRightBlock (retainedPassiveTransformedEdge A1 F2 A3 C p) =
        -(A1 p * F2 p.castSucc) ∧
      -((A1 p)⁻¹ *
          upperRightBlock (retainedPassiveTransformedEdge A1 F2 A3 C p)) =
        F2 p.castSucc ∧
      lowerLeftBlock (retainedPassiveTransformedEdge A1 F2 A3 C p) = A3 p ∧
      schurResidualBlock (retainedPassiveTransformedEdge A1 F2 A3 C p) =
        C p := by
  constructor
  · simp [retainedPassiveTransformedEdge]
  constructor
  · simp [retainedPassiveTransformedEdge]
  constructor
  · rw [retainedPassiveTransformedEdge, upperRightBlock_fromBlocks]
    rw [Matrix.mul_neg]
    calc
      - -((A1 p)⁻¹ * (A1 p * F2 p.castSucc)) =
          (A1 p)⁻¹ * (A1 p * F2 p.castSucc) := neg_neg _
      _ = F2 p.castSucc :=
          Matrix.nonsing_inv_mul_cancel_left
            (A := A1 p) (B := F2 p.castSucc) hA1
  constructor
  · simp [retainedPassiveTransformedEdge]
  · exact schurResidualBlock_retainedPassiveTransformedEdge A1 F2 A3 C p hA1

/-- One retained-passive step updates the suffix-state residual product by
multiplying with the prescribed residual block `C_p`. -/
theorem step_retainedPassiveFixedBaseEdgeMatrix_D
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (hB : S.B = -F2 p.succ)
    (hA1 : IsUnit (A1 p).det) :
    (step (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C) p S).D =
      S.D * C p := by
  have hM :=
    transformedEdge_retainedPassiveFixedBaseEdgeMatrix_of_B_eq
      A1 F2 A3 C p S hB
  simp [step, hM, schurResidualBlock_retainedPassiveTransformedEdge,
    hA1]

/-- One retained-passive step updates the suffix-state left multiplier by the
lower-unitriangular contribution from the prescribed `A3_p` block. -/
theorem step_retainedPassiveFixedBaseEdgeMatrix_L
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (hB : S.B = -F2 p.succ) :
    (step (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C) p S).L =
      fromBlocks (1 : Matrix ρ ρ K) 0
          (-(S.D * A3 p * (S.Ctop * A1 p)⁻¹))
          (1 : Matrix (κ j) (κ j) K) *
        S.L := by
  have hM :=
    transformedEdge_retainedPassiveFixedBaseEdgeMatrix_of_B_eq
      A1 F2 A3 C p S hB
  simp [step, hM, retainedPassiveTransformedEdge]

/-- If the next suffix-state left multiplier is lower unitriangular with lower
block `F3next`, one retained-passive step adds exactly the new lower-left
contribution from `A3_p`. -/
theorem step_retainedPassiveFixedBaseEdgeMatrix_lowerLeftBlock_L
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ K j p.succ)
    (F3next : Matrix (κ j) ρ K)
    (hB : S.B = -F2 p.succ)
    (hL :
      S.L = fromBlocks (1 : Matrix ρ ρ K) 0 F3next
        (1 : Matrix (κ j) (κ j) K)) :
    lowerLeftBlock
        (step (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C) p S).L =
      -(S.D * A3 p * (S.Ctop * A1 p)⁻¹) + F3next := by
  let X : Matrix (κ j) ρ K := -(S.D * A3 p * (S.Ctop * A1 p)⁻¹)
  have hLstep :
      (step (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C) p S).L =
        fromBlocks (1 : Matrix ρ ρ K) 0 X
            (1 : Matrix (κ j) (κ j) K) *
          S.L := by
    simpa [X] using
      step_retainedPassiveFixedBaseEdgeMatrix_L A1 F2 A3 C p S hB
  rw [hLstep, hL]
  rw [lowerUnitriangular_mul_fromBlocks_one_zero_indexed (K := K) X F3next]
  simp [lowerLeftBlock_fromBlocks, X]

/-- The deterministic suffix-state right field along retained-passive fixed-base
edges is the prescribed `-F2` field. -/
theorem suffixState_B_retainedPassiveFixedBaseEdgeMatrix
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    ∀ (i : Fin (N + 1)) (hi : i ≤ Fin.last N),
      (suffixState (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C)
        (Fin.last N) i hi).B = -F2 i := by
  let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
  let j : Fin (N + 1) := Fin.last N
  let motive : (m : ℕ) → m ≤ N → Prop := fun m hm ↦
    let i : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    (suffixState E j i (Fin.val_fin_le.mpr hm)).B = -F2 i
  have hbase : motive N le_rfl := by
    dsimp [motive]
    change (suffixState E (Fin.last N) (Fin.last N) le_rfl).B = -F2 (Fin.last N)
    simp [suffixState_self, terminal, hF2last]
  have hstep : ∀ m (hms : m + 1 ≤ N),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_le hms⟩
    have hstate :
        suffixState E j p.castSucc p.castSucc.le_last =
          step E p (suffixState E j p.succ p.succ.le_last) := by
      simpa [E, j, p] using
        suffixState_castSucc (K := K) E p p.succ.le_last
    have hBnext :
        (suffixState E j p.succ p.succ.le_last).B = -F2 p.succ := by
      simpa [motive, E, j, p] using ih
    have hBstep :
        (step E p (suffixState E j p.succ p.succ.le_last)).B =
          -F2 p.castSucc := by
      simpa [E] using
        step_retainedPassiveFixedBaseEdgeMatrix_B
          A1 F2 A3 C p (suffixState E j p.succ p.succ.le_last)
          hBnext (hA1 p)
    change (suffixState E j p.castSucc p.castSucc.le_last).B = -F2 p.castSucc
    rw [hstate]
    exact hBstep
  intro i hi
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, E, j] using hcanon

/-- The deterministic suffix-state residual field unfolds by multiplying the
prescribed retained-passive residual block. -/
theorem suffixState_D_retainedPassiveFixedBaseEdgeMatrix_castSucc
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det)
    (p : Fin N) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    (suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).D =
      (suffixState E (Fin.last N) p.succ p.succ.le_last).D * C p := by
  intro E
  have hstate :
      suffixState E (Fin.last N) p.castSucc p.castSucc.le_last =
        step E p (suffixState E (Fin.last N) p.succ p.succ.le_last) := by
    simpa [E] using suffixState_castSucc (K := K) E p p.succ.le_last
  have hB :
      (suffixState E (Fin.last N) p.succ p.succ.le_last).B = -F2 p.succ :=
    suffixState_B_retainedPassiveFixedBaseEdgeMatrix
      A1 F2 A3 C hF2last hA1 p.succ p.succ.le_last
  rw [hstate]
  exact
    step_retainedPassiveFixedBaseEdgeMatrix_D
      A1 F2 A3 C p (suffixState E (Fin.last N) p.succ p.succ.le_last)
      hB (hA1 p)

/-- Along retained-passive fixed-base edges, the deterministic suffix-state
residual field is the explicit ordered product of the prescribed residual
blocks. -/
theorem suffixState_D_retainedPassiveFixedBaseEdgeMatrix
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    ∀ (i : Fin (N + 1)) (hi : i ≤ Fin.last N),
      (suffixState (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C)
        (Fin.last N) i hi).D =
        residualFactorProduct C (Fin.last N) i hi := by
  let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
  let j : Fin (N + 1) := Fin.last N
  have hblock : ∀ (p : Fin N) (hpj : p.succ ≤ j),
      residualBlock E j p hpj = C p := by
    intro p hpj
    have hB :
        (suffixState E j p.succ hpj).B = -F2 p.succ :=
      suffixState_B_retainedPassiveFixedBaseEdgeMatrix
        A1 F2 A3 C hF2last hA1 p.succ hpj
    dsimp [residualBlock]
    rw [transformedEdge_retainedPassiveFixedBaseEdgeMatrix_of_B_eq
      A1 F2 A3 C p (suffixState E j p.succ hpj) hB]
    exact schurResidualBlock_retainedPassiveTransformedEdge
      A1 F2 A3 C p (hA1 p)
  intro i hi
  calc
    (suffixState E j i hi).D = residualProduct E j i hi := by
      exact suffixState_D_eq_residualProduct (K := K) E hi
    _ = residualFactorProduct C j i hi := by
      exact residualProduct_eq_residualFactorProduct_of_residualBlock_eq
        (K := K) E C hi hblock

/-- Along retained-passive fixed-base edges, the lower-left block of the
deterministic suffix-state left multiplier unfolds by adding the one-step
lower-unitriangular contribution. -/
theorem suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det)
    (p : Fin N) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    lowerLeftBlock
        (suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).L =
      -((suffixState E (Fin.last N) p.succ p.succ.le_last).D *
          A3 p *
          ((suffixState E (Fin.last N) p.succ p.succ.le_last).Ctop *
            A1 p)⁻¹) +
        lowerLeftBlock
          (suffixState E (Fin.last N) p.succ p.succ.le_last).L := by
  intro E
  let S : ChartLocalSuffixState ρ κ K (Fin.last N) p.succ :=
    suffixState E (Fin.last N) p.succ p.succ.le_last
  have hstate :
      suffixState E (Fin.last N) p.castSucc p.castSucc.le_last =
        step E p S := by
    simpa [E, S] using suffixState_castSucc (K := K) E p p.succ.le_last
  have hB : S.B = -F2 p.succ := by
    simpa [S, E] using
      suffixState_B_retainedPassiveFixedBaseEdgeMatrix
        A1 F2 A3 C hF2last hA1 p.succ p.succ.le_last
  rcases suffixState_L_eq_lowerUnitriangular (K := K) E p.succ.le_last with
    ⟨F3next, hL⟩
  have hlower :
      lowerLeftBlock (step E p S).L =
        -(S.D * A3 p * (S.Ctop * A1 p)⁻¹) + F3next := by
    simpa [E, S] using
      step_retainedPassiveFixedBaseEdgeMatrix_lowerLeftBlock_L
        A1 F2 A3 C p S F3next hB hL
  have hF3next : lowerLeftBlock S.L = F3next := by
    rw [hL]
    simp [lowerLeftBlock_fromBlocks]
  rw [hstate]
  rw [hF3next]
  exact hlower

/-- The same retained-passive lower-left recurrence, rewritten with the current
suffix-state top block `Ctop_p`. -/
theorem suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc_currentCtop
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det)
    (p : Fin N) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    lowerLeftBlock
        (suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).L =
      -((suffixState E (Fin.last N) p.succ p.succ.le_last).D *
          A3 p *
          ((suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).Ctop)⁻¹) +
        lowerLeftBlock
          (suffixState E (Fin.last N) p.succ p.succ.le_last).L := by
  intro E
  let S : ChartLocalSuffixState ρ κ K (Fin.last N) p.succ :=
    suffixState E (Fin.last N) p.succ p.succ.le_last
  have hstate :
      suffixState E (Fin.last N) p.castSucc p.castSucc.le_last =
        step E p S := by
    simpa [E, S] using suffixState_castSucc (K := K) E p p.succ.le_last
  have hB : S.B = -F2 p.succ := by
    simpa [S, E] using
      suffixState_B_retainedPassiveFixedBaseEdgeMatrix
        A1 F2 A3 C hF2last hA1 p.succ p.succ.le_last
  have hCtop :
      (suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).Ctop =
        S.Ctop * A1 p := by
    rw [hstate]
    exact step_retainedPassiveFixedBaseEdgeMatrix_Ctop A1 F2 A3 C p S hB
  have hrec :=
    suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc
      A1 F2 A3 C hF2last hA1 p
  rw [hCtop]
  exact hrec

/-- The finite tail sum obtained by iterating the retained-passive lower-left
`L` recurrence from index `m` to the terminal suffix state.

The summand at edge `p` is the one-edge contribution
`-(D_{p+1} * A3_p * Ctop_p⁻¹)`, expressed using the actual deterministic
suffix states. -/
def retainedPassiveLowerLeftTailSum
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (m : ℕ) (hm : m ≤ N) : Matrix (κ (Fin.last N)) ρ K :=
  let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
  Nat.decreasingInduction
    (motive := fun _ _ ↦ Matrix (κ (Fin.last N)) ρ K)
    (fun q hqs acc ↦
      let p : Fin N := ⟨q, Nat.lt_of_succ_le hqs⟩;
      -((suffixState E (Fin.last N) p.succ p.succ.le_last).D *
          A3 p *
          ((suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).Ctop)⁻¹) +
        acc)
    0
    hm

/-- The retained-passive lower-left tail sum is zero at the terminal suffix
state. -/
@[simp]
theorem retainedPassiveLowerLeftTailSum_self
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K) :
    retainedPassiveLowerLeftTailSum A1 F2 A3 C N le_rfl = 0 := by
  simp [retainedPassiveLowerLeftTailSum]

/-- The retained-passive lower-left tail sum unfolds by adding the contribution
from the current edge and then continuing with the successor suffix. -/
theorem retainedPassiveLowerLeftTailSum_castSucc
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (p : Fin N) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    retainedPassiveLowerLeftTailSum A1 F2 A3 C p.val (Nat.le_of_lt p.isLt) =
      -((suffixState E (Fin.last N) p.succ p.succ.le_last).D *
          A3 p *
          ((suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).Ctop)⁻¹) +
        retainedPassiveLowerLeftTailSum A1 F2 A3 C (p.val + 1)
          (Nat.succ_le_of_lt p.isLt) := by
  intro E
  unfold retainedPassiveLowerLeftTailSum
  rw [Nat.decreasingInduction_succ_left]

/-- Along retained-passive fixed-base edges, the lower-left block of the
deterministic suffix-state left multiplier is the finite tail sum of all
one-edge lower-left contributions to its right. -/
theorem suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    ∀ (i : Fin (N + 1)) (hi : i ≤ Fin.last N),
      let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
      lowerLeftBlock (suffixState E (Fin.last N) i hi).L =
        retainedPassiveLowerLeftTailSum A1 F2 A3 C i.val (Fin.val_fin_le.mp hi) := by
  let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
  let j : Fin (N + 1) := Fin.last N
  let motive : (m : ℕ) → m ≤ N → Prop := fun m hm ↦
    let i : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    lowerLeftBlock (suffixState E j i (Fin.val_fin_le.mpr hm)).L =
      retainedPassiveLowerLeftTailSum A1 F2 A3 C m hm
  have hbase : motive N le_rfl := by
    dsimp [motive]
    have hll_one :
        lowerLeftBlock (1 : Matrix (ρ ⊕ κ j) (ρ ⊕ κ j) K) =
          (0 : Matrix (κ j) ρ K) := by
      ext a b
      simp [lowerLeftBlock]
    change lowerLeftBlock (suffixState E j j le_rfl).L =
      retainedPassiveLowerLeftTailSum A1 F2 A3 C N le_rfl
    simp [retainedPassiveLowerLeftTailSum, E, j, suffixState_self, terminal,
      hll_one]
  have hstep : ∀ m (hms : m + 1 ≤ N),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_le hms⟩
    have hm : m ≤ N := Nat.le_of_succ_le hms
    have hrec :
        lowerLeftBlock (suffixState E j p.castSucc p.castSucc.le_last).L =
          -((suffixState E j p.succ p.succ.le_last).D *
              A3 p *
              ((suffixState E j p.castSucc p.castSucc.le_last).Ctop)⁻¹) +
            lowerLeftBlock (suffixState E j p.succ p.succ.le_last).L := by
      simpa [E, j, p] using
        suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc_currentCtop
          A1 F2 A3 C hF2last hA1 p
    have ih' :
        lowerLeftBlock (suffixState E j p.succ p.succ.le_last).L =
          retainedPassiveLowerLeftTailSum A1 F2 A3 C (m + 1) hms := by
      simpa [motive, E, j, p] using ih
    have htail :
        retainedPassiveLowerLeftTailSum A1 F2 A3 C m hm =
          -((suffixState E j p.succ p.succ.le_last).D *
              A3 p *
              ((suffixState E j p.castSucc p.castSucc.le_last).Ctop)⁻¹) +
            retainedPassiveLowerLeftTailSum A1 F2 A3 C (m + 1) hms := by
      unfold retainedPassiveLowerLeftTailSum
      rw [Nat.decreasingInduction_succ_left]
    change lowerLeftBlock (suffixState E j p.castSucc p.castSucc.le_last).L =
      retainedPassiveLowerLeftTailSum A1 F2 A3 C m hm
    rw [hrec, ih', htail]
  intro i hi
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, E, j] using hcanon

/-- Source-left-endpoint specialization of the retained-passive lower-left tail
sum formula. -/
theorem suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_tailSum
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    lowerLeftBlock
        (suffixState E (Fin.last N) 0 (Fin.zero_le (Fin.last N))).L =
      retainedPassiveLowerLeftTailSum A1 F2 A3 C 0 (Nat.zero_le N) := by
  intro E
  simpa [E] using
    suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum
      A1 F2 A3 C hF2last hA1 (0 : Fin (N + 1)) (Fin.zero_le (Fin.last N))

/-- The deterministic suffix-state top block unfolds by multiplying the
prescribed retained-passive `A1_p` block. -/
theorem suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det)
    (p : Fin N) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    (suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).Ctop =
      (suffixState E (Fin.last N) p.succ p.succ.le_last).Ctop * A1 p := by
  intro E
  have hstate :
      suffixState E (Fin.last N) p.castSucc p.castSucc.le_last =
        step E p (suffixState E (Fin.last N) p.succ p.succ.le_last) := by
    simpa [E] using suffixState_castSucc (K := K) E p p.succ.le_last
  have hB :
      (suffixState E (Fin.last N) p.succ p.succ.le_last).B = -F2 p.succ :=
    suffixState_B_retainedPassiveFixedBaseEdgeMatrix
      A1 F2 A3 C hF2last hA1 p.succ p.succ.le_last
  rw [hstate]
  exact
    step_retainedPassiveFixedBaseEdgeMatrix_Ctop
      A1 F2 A3 C p (suffixState E (Fin.last N) p.succ p.succ.le_last) hB

/-- Along retained-passive fixed-base edges, the deterministic suffix-state top
block is the ordered product of the prescribed retained-passive `A1` factors. -/
theorem suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    ∀ (i : Fin (N + 1)) (hi : i ≤ Fin.last N),
      (suffixState (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C)
        (Fin.last N) i hi).Ctop =
        residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
          A1 (Fin.last N) i hi := by
  let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
  let j : Fin (N + 1) := Fin.last N
  let motive : (m : ℕ) → m ≤ N → Prop := fun m hm ↦
    let i : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    (suffixState E j i (Fin.val_fin_le.mpr hm)).Ctop =
      residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
        A1 j i (Fin.val_fin_le.mpr hm)
  have hbase : motive N le_rfl := by
    dsimp [motive]
    change (suffixState E j j le_rfl).Ctop =
      residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
        A1 j j le_rfl
    simp [suffixState_self, terminal]
  have hstep : ∀ m (hms : m + 1 ≤ N),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_le hms⟩
    have hCtop :
        (suffixState E j p.castSucc p.castSucc.le_last).Ctop =
          (suffixState E j p.succ p.succ.le_last).Ctop * A1 p := by
      simpa [E, j, p] using
        suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc
          A1 F2 A3 C hF2last hA1 p
    have ih' :
        (suffixState E j p.succ p.succ.le_last).Ctop =
          residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
            A1 j p.succ p.succ.le_last := by
      simpa [motive, E, j, p] using ih
    have hprod :
        residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
            A1 j p.castSucc p.castSucc.le_last =
          residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
              A1 j p.succ p.succ.le_last * A1 p := by
      simpa [j, p] using
        residualFactorProduct_castSucc (K := K)
          (κ := fun _ : Fin (N + 1) ↦ ρ) A1 (j := j) p p.succ.le_last
    change (suffixState E j p.castSucc p.castSucc.le_last).Ctop =
      residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
        A1 j p.castSucc p.castSucc.le_last
    rw [hCtop, ih', hprod]
  intro i hi
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, E, j] using hcanon

/-- The retained-passive lower-left tail sum with suffix-state fields replaced
by explicit ordered products of the prescribed `C` and `A1` factors. -/
def retainedPassiveLowerLeftProductTailSum
    (A1 : Fin N → Matrix ρ ρ K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (m : ℕ) (hm : m ≤ N) : Matrix (κ (Fin.last N)) ρ K :=
  Nat.decreasingInduction
    (motive := fun _ _ ↦ Matrix (κ (Fin.last N)) ρ K)
    (fun q hqs acc ↦
      let p : Fin N := ⟨q, Nat.lt_of_succ_le hqs⟩;
      -(residualFactorProduct C (Fin.last N) p.succ p.succ.le_last *
          A3 p *
          (residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
            A1 (Fin.last N) p.castSucc p.castSucc.le_last)⁻¹) +
        acc)
    0
    hm

/-- The explicit retained-passive lower-left product-tail sum is zero at the
terminal suffix state. -/
@[simp]
theorem retainedPassiveLowerLeftProductTailSum_self
    (A1 : Fin N → Matrix ρ ρ K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K) :
    retainedPassiveLowerLeftProductTailSum A1 A3 C N le_rfl = 0 := by
  simp [retainedPassiveLowerLeftProductTailSum]

/-- The explicit retained-passive lower-left product-tail sum unfolds by the
current product summand and the successor tail. -/
theorem retainedPassiveLowerLeftProductTailSum_castSucc
    (A1 : Fin N → Matrix ρ ρ K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (p : Fin N) :
    retainedPassiveLowerLeftProductTailSum A1 A3 C p.val (Nat.le_of_lt p.isLt) =
      -(residualFactorProduct C (Fin.last N) p.succ p.succ.le_last *
          A3 p *
          (residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
            A1 (Fin.last N) p.castSucc p.castSucc.le_last)⁻¹) +
        retainedPassiveLowerLeftProductTailSum A1 A3 C (p.val + 1)
          (Nat.succ_le_of_lt p.isLt) := by
  unfold retainedPassiveLowerLeftProductTailSum
  rw [Nat.decreasingInduction_succ_left]

/-- In a nonempty retained-passive edge family, the explicit lower-left product
tail at the final edge is just the final `A3` contribution. -/
theorem retainedPassiveLowerLeftProductTailSum_last
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K) :
    retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
        A1 A3 C M (Nat.le_succ M) =
      -((1 : Matrix (κ' (Fin.last M).succ) (κ' (Fin.last M).succ) K) *
          A3 (Fin.last M) *
          (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1 (Fin.last (M + 1)) (Fin.last M).castSucc
              (Fin.last M).castSucc.le_last)⁻¹) := by
  have h :=
    retainedPassiveLowerLeftProductTailSum_castSucc
      (K := K) (ρ := ρ) (κ := κ') A1 A3 C (Fin.last M)
  simpa [Matrix.one_mul] using h

/-- In a nonempty retained-passive edge family, setting the final lower-left
block to `-G*Ctop_last` realizes the target final tail value `G`. -/
theorem retainedPassiveLowerLeftProductTailSum_last_eq_of_A3_eq_neg_target_mul_Ctop
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (G : Matrix (κ' (Fin.last (M + 1))) ρ K) :
    let CtopLast : Matrix ρ ρ K :=
      residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 (Fin.last (M + 1)) (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last
    IsUnit CtopLast.det →
      A3 (Fin.last M) = -G * CtopLast →
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3 C M (Nat.le_succ M) = G := by
  intro CtopLast hCtop hA3last
  have hlast :=
    retainedPassiveLowerLeftProductTailSum_last
      (K := K) (ρ := ρ) (κ' := κ') A1 A3 C
  have htail :
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
        A1 A3 C M (Nat.le_succ M) =
          -((1 : Matrix (κ' (Fin.last M).succ) (κ' (Fin.last M).succ) K) *
              A3 (Fin.last M) * CtopLast⁻¹) := by
    simpa [CtopLast] using hlast
  rw [htail]
  rw [Matrix.one_mul]
  rw [hA3last]
  calc
    -((-G * CtopLast) * CtopLast⁻¹) =
        -(-G * (CtopLast * CtopLast⁻¹)) := by
          rw [Matrix.mul_assoc]
    _ = -(-G * (1 : Matrix ρ ρ K)) := by
          rw [Matrix.mul_nonsing_inv CtopLast hCtop]
    _ = -(-G) := by rw [Matrix.mul_one]
    _ = G := by exact neg_neg G

/-- The final-edge-zeroed `A3` family keeps all lower-left blocks except the
last one.  Its product tail is the signed contribution of the earlier edges. -/
def retainedPassiveA3WithoutLast
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (p : Fin (M + 1)) : Matrix (κ' p.succ) ρ K :=
  if p = Fin.last M then 0 else A3 p

omit [Fintype ρ] [DecidableEq ρ] in
@[simp]
theorem retainedPassiveA3WithoutLast_last
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K) :
    retainedPassiveA3WithoutLast (K := K) (ρ := ρ) (κ' := κ') A3 (Fin.last M) = 0 := by
  simp [retainedPassiveA3WithoutLast]

omit [Fintype ρ] [DecidableEq ρ] in
theorem retainedPassiveA3WithoutLast_eq_of_ne
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    {p : Fin (M + 1)} (hp : p ≠ Fin.last M) :
    retainedPassiveA3WithoutLast (K := K) (ρ := ρ) (κ' := κ') A3 p = A3 p := by
  simp [retainedPassiveA3WithoutLast, hp]

/-- The product tail with the final `A3` block zeroed has zero final-edge tail. -/
@[simp]
theorem retainedPassiveLowerLeftProductTailSum_withoutLast_last
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K) :
    retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
        A1 (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3) C M (Nat.le_succ M) =
      0 := by
  have hlast :=
    retainedPassiveLowerLeftProductTailSum_last
      (K := K) (ρ := ρ) (κ' := κ')
      A1 (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3) C
  rw [hlast, retainedPassiveA3WithoutLast_last]
  rw [show
      (1 : Matrix (κ' (Fin.last M).succ) (κ' (Fin.last M).succ) K) *
          (0 : Matrix (κ' (Fin.last M).succ) ρ K) = 0 by
        exact Matrix.mul_zero _]
  rw [Matrix.zero_mul]
  exact neg_zero

/-- Splitting the explicit product tail into the signed earlier-edge tail and
the final-edge tail. -/
theorem retainedPassiveLowerLeftProductTailSum_eq_withoutLast_add_last
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K) :
    ∀ (m : ℕ) (hm : m ≤ M),
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3 C m (Nat.le_trans hm (Nat.le_succ M)) =
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
            A1 (retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3) C m
              (Nat.le_trans hm (Nat.le_succ M)) +
          retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
            A1 A3 C M (Nat.le_succ M) := by
  let A3early := retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3
  let lastTail :=
    retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
      A1 A3 C M (Nat.le_succ M)
  let motive : (m : ℕ) → m ≤ M → Prop := fun m hm ↦
    retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
        A1 A3 C m (Nat.le_trans hm (Nat.le_succ M)) =
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3early C m (Nat.le_trans hm (Nat.le_succ M)) + lastTail
  have hbase : motive M le_rfl := by
    dsimp [motive, lastTail, A3early]
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin (M + 1) :=
      ⟨m, Nat.lt_trans (Nat.lt_of_succ_le hms) (Nat.lt_succ_self M)⟩
    have hp_ne : p ≠ Fin.last M := by
      intro hp
      have hval : p.val = (Fin.last M).val := congrArg Fin.val hp
      simp [p] at hval
      omega
    have htail :
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
            A1 A3 C m
              (Nat.le_trans (Nat.le_of_succ_le hms) (Nat.le_succ M)) =
          -(residualFactorProduct C (Fin.last (M + 1)) p.succ p.succ.le_last *
              A3 p *
              (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                A1 (Fin.last (M + 1)) p.castSucc p.castSucc.le_last)⁻¹) +
            retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
              A1 A3 C (m + 1) (Nat.le_trans hms (Nat.le_succ M)) := by
      simpa [p] using
        retainedPassiveLowerLeftProductTailSum_castSucc
          (K := K) (ρ := ρ) (κ := κ') A1 A3 C p
    have htailEarly :
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
            A1 A3early C m
              (Nat.le_trans (Nat.le_of_succ_le hms) (Nat.le_succ M)) =
          -(residualFactorProduct C (Fin.last (M + 1)) p.succ p.succ.le_last *
              A3 p *
              (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
                A1 (Fin.last (M + 1)) p.castSucc p.castSucc.le_last)⁻¹) +
            retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
              A1 A3early C (m + 1) (Nat.le_trans hms (Nat.le_succ M)) := by
      have hcast :=
        retainedPassiveLowerLeftProductTailSum_castSucc
          (K := K) (ρ := ρ) (κ := κ') A1 A3early C p
      have hA3p : A3early p = A3 p := by
        simpa [A3early] using
          retainedPassiveA3WithoutLast_eq_of_ne (K := K) (ρ := ρ) A3 hp_ne
      simpa [p, hA3p] using hcast
    change retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
        A1 A3 C m (Nat.le_trans (Nat.le_of_succ_le hms) (Nat.le_succ M)) =
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3early C m
            (Nat.le_trans (Nat.le_of_succ_le hms) (Nat.le_succ M)) + lastTail
    rw [htail, htailEarly, ih]
    simp [add_assoc]
  intro m hm
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase hm
  simpa [motive, A3early, lastTail] using hcanon

/-- If the final lower-left block is chosen from the active source target
`F3` plus the unsigned earlier-edge prefix, then the source product tail is
`F3`.  The earlier prefix is represented as the negative of the signed product
tail with the final `A3` block zeroed. -/
theorem retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K) :
    let A3early := retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3
    let earlyTail : Matrix (κ' (Fin.last (M + 1))) ρ K :=
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
        A1 A3early C 0 (Nat.zero_le (M + 1))
    let CtopLast : Matrix ρ ρ K :=
      residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 (Fin.last (M + 1)) (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last
    IsUnit CtopLast.det →
      A3 (Fin.last M) = -(F3 - earlyTail) * CtopLast →
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3 C 0 (Nat.zero_le (M + 1)) = F3 := by
  intro A3early earlyTail CtopLast hCtop hA3last
  have hsplit :
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3 C 0 (Nat.zero_le (M + 1)) =
        earlyTail +
          retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
            A1 A3 C M (Nat.le_succ M) := by
    simpa [A3early, earlyTail] using
      retainedPassiveLowerLeftProductTailSum_eq_withoutLast_add_last
        (K := K) (ρ := ρ) (κ' := κ') A1 A3 C 0 (Nat.zero_le M)
  have hlast :
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3 C M (Nat.le_succ M) =
        F3 - earlyTail := by
    simpa [CtopLast] using
      retainedPassiveLowerLeftProductTailSum_last_eq_of_A3_eq_neg_target_mul_Ctop
        (K := K) (ρ := ρ) (κ' := κ') A1 A3 C (F3 - earlyTail) hCtop hA3last
  rw [hsplit, hlast]
  simp [sub_eq_add_neg, add_left_comm]

/-- The suffix-state retained-passive lower-left tail sum is the same as the
explicit product-tail sum once `D` and `Ctop` are read back from the recursive
suffix state. -/
theorem retainedPassiveLowerLeftTailSum_eq_productTailSum
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    ∀ (m : ℕ) (hm : m ≤ N),
      retainedPassiveLowerLeftTailSum A1 F2 A3 C m hm =
        retainedPassiveLowerLeftProductTailSum A1 A3 C m hm := by
  let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
  let j : Fin (N + 1) := Fin.last N
  let motive : (m : ℕ) → m ≤ N → Prop := fun m hm ↦
    retainedPassiveLowerLeftTailSum A1 F2 A3 C m hm =
      retainedPassiveLowerLeftProductTailSum A1 A3 C m hm
  have hbase : motive N le_rfl := by
    simp [motive]
  have hstep : ∀ m (hms : m + 1 ≤ N),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_le hms⟩
    have hm : m ≤ N := Nat.le_of_succ_le hms
    have htail :
        retainedPassiveLowerLeftTailSum A1 F2 A3 C m hm =
          -((suffixState E j p.succ p.succ.le_last).D *
              A3 p *
              ((suffixState E j p.castSucc p.castSucc.le_last).Ctop)⁻¹) +
            retainedPassiveLowerLeftTailSum A1 F2 A3 C (m + 1) hms := by
      simpa [E, j, p, hm] using
        retainedPassiveLowerLeftTailSum_castSucc A1 F2 A3 C p
    have hproductTail :
        retainedPassiveLowerLeftProductTailSum A1 A3 C m hm =
          -(residualFactorProduct C j p.succ p.succ.le_last *
              A3 p *
              (residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
                A1 j p.castSucc p.castSucc.le_last)⁻¹) +
            retainedPassiveLowerLeftProductTailSum A1 A3 C (m + 1) hms := by
      simpa [j, p, hm] using
        retainedPassiveLowerLeftProductTailSum_castSucc A1 A3 C p
    have hD :
        (suffixState E j p.succ p.succ.le_last).D =
          residualFactorProduct C j p.succ p.succ.le_last := by
      simpa [E, j, p] using
        suffixState_D_retainedPassiveFixedBaseEdgeMatrix
          A1 F2 A3 C hF2last hA1 p.succ p.succ.le_last
    have hCtop :
        (suffixState E j p.castSucc p.castSucc.le_last).Ctop =
          residualFactorProduct (K := K) (κ := fun _ : Fin (N + 1) ↦ ρ)
            A1 j p.castSucc p.castSucc.le_last := by
      simpa [E, j, p] using
        suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix
          A1 F2 A3 C hF2last hA1 p.castSucc p.castSucc.le_last
    change retainedPassiveLowerLeftTailSum A1 F2 A3 C m hm =
      retainedPassiveLowerLeftProductTailSum A1 A3 C m hm
    rw [htail, hproductTail, hD, hCtop, ih]
  intro m hm
  exact Nat.decreasingInduction (motive := motive) hstep hbase hm

/-- Along retained-passive fixed-base edges, the lower-left block of the
deterministic suffix-state left multiplier is the explicit product-tail sum of
all one-edge lower-left contributions to its right. -/
theorem suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_productTailSum
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    ∀ (i : Fin (N + 1)) (hi : i ≤ Fin.last N),
      let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
      lowerLeftBlock (suffixState E (Fin.last N) i hi).L =
        retainedPassiveLowerLeftProductTailSum A1 A3 C i.val (Fin.val_fin_le.mp hi) := by
  intro i hi E
  calc
    lowerLeftBlock (suffixState E (Fin.last N) i hi).L =
        retainedPassiveLowerLeftTailSum A1 F2 A3 C i.val (Fin.val_fin_le.mp hi) := by
      simpa [E] using
        suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum
          A1 F2 A3 C hF2last hA1 i hi
    _ = retainedPassiveLowerLeftProductTailSum A1 A3 C i.val (Fin.val_fin_le.mp hi) := by
      exact retainedPassiveLowerLeftTailSum_eq_productTailSum
        A1 F2 A3 C hF2last hA1 i.val (Fin.val_fin_le.mp hi)

/-- Source-left-endpoint specialization of the explicit retained-passive
lower-left product-tail formula. -/
theorem suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_productTailSum
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    lowerLeftBlock
        (suffixState E (Fin.last N) 0 (Fin.zero_le (Fin.last N))).L =
      retainedPassiveLowerLeftProductTailSum A1 A3 C 0 (Nat.zero_le N) := by
  intro E
  simpa [E] using
    suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_productTailSum
      A1 F2 A3 C hF2last hA1 (0 : Fin (N + 1)) (Fin.zero_le (Fin.last N))

/-- Along retained-passive fixed-base edges, the deterministic suffix-state top
block stays in the determinant-unit chart when every `A1_p` is a unit. -/
theorem suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det) :
    ∀ (i : Fin (N + 1)) (hi : i ≤ Fin.last N),
      IsUnit
        ((suffixState (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C)
          (Fin.last N) i hi).Ctop).det := by
  let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
  let j : Fin (N + 1) := Fin.last N
  let motive : (m : ℕ) → m ≤ N → Prop := fun m hm ↦
    let i : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    IsUnit ((suffixState E j i (Fin.val_fin_le.mpr hm)).Ctop).det
  have hbase : motive N le_rfl := by
    dsimp [motive]
    change IsUnit ((suffixState E (Fin.last N) (Fin.last N) le_rfl).Ctop).det
    simp [suffixState_self, terminal]
  have hstep : ∀ m (hms : m + 1 ≤ N),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih
    let p : Fin N := ⟨m, Nat.lt_of_succ_le hms⟩
    have hCtop :
        (suffixState E j p.castSucc p.castSucc.le_last).Ctop =
          (suffixState E j p.succ p.succ.le_last).Ctop * A1 p := by
      simpa [E, j, p] using
        suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc
          A1 F2 A3 C hF2last hA1 p
    have ih' : IsUnit ((suffixState E j p.succ p.succ.le_last).Ctop).det := by
      simpa [motive, E, j, p] using ih
    change IsUnit ((suffixState E j p.castSucc p.castSucc.le_last).Ctop).det
    rw [hCtop]
    simpa [Matrix.det_mul] using ih'.mul (hA1 p)
  intro i hi
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase (Fin.val_fin_le.mp hi)
  simpa [motive, E, j] using hcanon

/-- Constructor-side readback for the full retained-passive `A1` family.

For fixed-base edges built from a full determinant-unit family `A1`, adjacent
recursive suffix-state top blocks recover the supplied factor
`A1_p = Ctop_{p+1}⁻¹ * Ctop_p`.

At `p = 0` this is only the finite algebra underlying the later active endpoint
formula.  It is not yet the retained-passive coordinate-domain theorem: here
`A1_0` is still part of the input family, and `hA1` assumes its determinant is
a unit. -/
theorem retainedPassiveFixedBaseEdgeMatrix_A1_eq_suffixState_Ctop_inv_mul_Ctop
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det)
    (p : Fin N) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    A1 p =
      ((suffixState E (Fin.last N) p.succ p.succ.le_last).Ctop)⁻¹ *
        (suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).Ctop := by
  intro E
  have hCtop :
      (suffixState E (Fin.last N) p.castSucc p.castSucc.le_last).Ctop =
        (suffixState E (Fin.last N) p.succ p.succ.le_last).Ctop * A1 p := by
    simpa [E] using
      suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc
        A1 F2 A3 C hF2last hA1 p
  have hCtop_next :
      IsUnit ((suffixState E (Fin.last N) p.succ p.succ.le_last).Ctop).det := by
    simpa [E] using
      suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix
        A1 F2 A3 C hF2last hA1 p.succ p.succ.le_last
  rw [hCtop]
  simp [Matrix.nonsing_inv_mul_cancel_left, hCtop_next]

/-- The retained-passive passive top-left tail after the first edge:
`A1_last * ... * A1_1`, with the empty product equal to `1` in the
single-edge case. -/
def retainedPassiveA1TailAfterFirst
    {M : ℕ}
    (A1 : Fin (M + 1) → Matrix ρ ρ K) : Matrix ρ ρ K :=
  residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
    A1 (Fin.last (M + 1)) (0 : Fin (M + 1)).succ
      (0 : Fin (M + 1)).succ.le_last

/-- The full retained-passive top-left product splits as the passive tail after
the first edge times the first `A1` block. -/
theorem retainedPassiveA1TailAfterFirst_mul_first
    {M : ℕ}
    (A1 : Fin (M + 1) → Matrix ρ ρ K) :
    residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1))) =
      retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1 * A1 0 := by
  have h :=
    residualFactorProduct_castSucc (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
      A1 (j := Fin.last (M + 1)) (0 : Fin (M + 1))
        (0 : Fin (M + 1)).succ.le_last
  simpa [retainedPassiveA1TailAfterFirst] using h

/-- The passive top-left tail after the first edge is determinant-unit when
each passive `A1_p`, `p ≠ 0`, is determinant-unit. -/
theorem retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
    {M : ℕ}
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (hPassive : ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (A1 p).det) :
    IsUnit (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1).det := by
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    1 ≤ m →
      IsUnit
        (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1 j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)).det
  have hbase : motive (M + 1) le_rfl := by
    intro _hmpos
    change IsUnit
      (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 j j le_rfl).det
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih hmpos
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hp_ne : p ≠ 0 := by
      intro hp
      have hval : p.val = (0 : Fin (M + 1)).val := congrArg Fin.val hp
      simp [p] at hval
      omega
    have hprod :
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1 j p.castSucc p.castSucc.le_last =
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
              A1 j p.succ p.succ.le_last * A1 p := by
      simpa [j, p] using
        residualFactorProduct_castSucc (K := K)
          (κ := fun _ : Fin (M + 2) ↦ ρ) A1 (j := j) p p.succ.le_last
    have ih' :
        IsUnit
          (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1 j p.succ p.succ.le_last).det := by
      have hmpos_succ : 1 ≤ m + 1 := Nat.succ_pos m
      simpa [motive, j, p] using ih hmpos_succ
    change IsUnit
      (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 j p.castSucc p.castSucc.le_last).det
    rw [hprod]
    simpa [Matrix.det_mul] using ih'.mul (hPassive p hp_ne)
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase
      (Nat.succ_le_succ (Nat.zero_le M))
  have htail := hcanon le_rfl
  simpa [retainedPassiveA1TailAfterFirst, motive, j] using htail

/-- If the first top-left block is solved as `Tail^{-1} * Ctop`, then the full
retained-passive top-left product realizes the active endpoint `Ctop`. -/
theorem retainedPassiveCtopProduct_zero_eq_target_of_A1_zero_eq
    {M : ℕ}
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K)
    (hTail : IsUnit (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1).det)
    (hA10 :
      A1 0 = (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹ * Ctop) :
    residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1))) = Ctop := by
  rw [retainedPassiveA1TailAfterFirst_mul_first]
  rw [hA10]
  calc
    retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1 *
        ((retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹ * Ctop) =
      (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1 *
          (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹) * Ctop := by
        rw [Matrix.mul_assoc]
    _ = (1 : Matrix ρ ρ K) * Ctop := by
        rw [Matrix.mul_nonsing_inv _ hTail]
    _ = Ctop := by rw [Matrix.one_mul]

/-- The solved first top-left block is determinant-unit when the passive tail
and active endpoint are determinant-unit. -/
theorem retainedPassiveA1_zero_det_isUnit_of_A1_zero_eq_tail_inv_mul
    {M : ℕ}
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K)
    (hTail : IsUnit (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1).det)
    (hCtop : IsUnit Ctop.det)
    (hA10 :
      A1 0 = (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹ * Ctop) :
    IsUnit (A1 0).det := by
  rw [hA10]
  have hTailInv :
      IsUnit ((retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹).det :=
    (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1).isUnit_nonsing_inv_det hTail
  simpa [Matrix.det_mul] using hTailInv.mul hCtop

/-- The retained-passive full `A1` family is determinant-unit when the passive
blocks are determinant-unit and the solved first block comes from a unit tail
and unit active endpoint. -/
theorem retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul
    {M : ℕ}
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K)
    (hPassive : ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (A1 p).det)
    (hCtop : IsUnit Ctop.det)
    (hA10 :
      A1 0 = (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹ * Ctop) :
    ∀ p : Fin (M + 1), IsUnit (A1 p).det := by
  have hTail : IsUnit (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1).det :=
    retainedPassiveA1TailAfterFirst_det_isUnit_of_passive (K := K) (ρ := ρ) A1 hPassive
  intro p
  by_cases hp : p = 0
  · subst p
    exact
      retainedPassiveA1_zero_det_isUnit_of_A1_zero_eq_tail_inv_mul
        (K := K) (ρ := ρ) A1 Ctop hTail hCtop hA10
  · exact hPassive p hp

/-- For retained-passive fixed-base edges, solving `A1_0` from the passive tail
and active `Ctop` makes the deterministic source-left top block equal to the
active endpoint. -/
theorem suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_zero_eq_target_of_A1_zero_eq
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (M + 2), Matrix ρ (κ' i) K)
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (Ctop : Matrix ρ ρ K)
    (hF2last : F2 (Fin.last (M + 1)) = 0)
    (hPassive : ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (A1 p).det)
    (hCtop : IsUnit Ctop.det)
    (hA10 :
      A1 0 = (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹ * Ctop) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    (suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).Ctop = Ctop := by
  intro E
  have hA1 : ∀ p : Fin (M + 1), IsUnit (A1 p).det :=
    retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul
      (K := K) (ρ := ρ) A1 Ctop hPassive hCtop hA10
  have hTail : IsUnit (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1).det :=
    retainedPassiveA1TailAfterFirst_det_isUnit_of_passive (K := K) (ρ := ρ) A1 hPassive
  calc
    (suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).Ctop =
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1 (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1))) := by
      simpa [E] using
        suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix
          (K := K) (ρ := ρ) (κ := κ') A1 F2 A3 C hF2last hA1
          (0 : Fin (M + 2)) (Fin.zero_le (Fin.last (M + 1)))
    _ = Ctop := by
      exact
        retainedPassiveCtopProduct_zero_eq_target_of_A1_zero_eq
          (K := K) (ρ := ρ) A1 Ctop hTail hA10

/-- Retained-passive fixed-base edge matrices have the prescribed transformed
edge at every step of the deterministic suffix-state recursion. -/
theorem retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det)
    (p : Fin N) :
    transformedEdge (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C) p
        (suffixState (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C)
          (Fin.last N) p.succ p.succ.le_last) =
      retainedPassiveTransformedEdge A1 F2 A3 C p := by
  have hB :=
    suffixState_B_retainedPassiveFixedBaseEdgeMatrix
      A1 F2 A3 C hF2last hA1 p.succ p.succ.le_last
  exact
    transformedEdge_retainedPassiveFixedBaseEdgeMatrix_of_B_eq
      A1 F2 A3 C p
      (suffixState (retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C)
        (Fin.last N) p.succ p.succ.le_last)
      hB

/-- For retained-passive fixed-base edges, the one-step chart readbacks of the
actual deterministic transformed edge recover the supplied coordinate blocks. -/
theorem retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks
    (A1 : Fin N → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (N + 1), Matrix ρ (κ i) K)
    (A3 : ∀ p : Fin N, Matrix (κ p.succ) ρ K)
    (C : ∀ p : Fin N, Matrix (κ p.succ) (κ p.castSucc) K)
    (hF2last : F2 (Fin.last N) = 0)
    (hA1 : ∀ p : Fin N, IsUnit (A1 p).det)
    (p : Fin N) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
    let M := transformedEdge E p
      (suffixState E (Fin.last N) p.succ p.succ.le_last)
    topLeftCorner M = A1 p ∧
      upperRightBlock M = -(A1 p * F2 p.castSucc) ∧
      -((A1 p)⁻¹ * upperRightBlock M) = F2 p.castSucc ∧
      lowerLeftBlock M = A3 p ∧
      schurResidualBlock M = C p := by
  intro E M
  have hM :
      M = retainedPassiveTransformedEdge A1 F2 A3 C p := by
    simpa [E, M] using
      retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq
        A1 F2 A3 C hF2last hA1 p
  rw [hM]
  exact retainedPassiveTransformedEdge_readbacks A1 F2 A3 C p (hA1 p)

/-- Retained-passive fixed-base edges with the solved endpoint blocks read back
the active source-left fields `F2_0`, `Ctop`, and `F3`, and still have the
prescribed transformed edge at every step.

This is a finite fixed-base endpoint package.  It does not assert source-rank
coverage, a source/image theorem, density, Jacobian accounting, normal
crossings, pole order, or RLCT. -/
theorem retainedPassiveFixedBaseEdgeMatrix_activeEndpointFields_eq_targets
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (M + 2), Matrix ρ (κ' i) K)
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (Ctop : Matrix ρ ρ K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K)
    (hF2last : F2 (Fin.last (M + 1)) = 0)
    (hPassiveA1 : ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (A1 p).det)
    (hCtop : IsUnit Ctop.det)
    (hA10 :
      A1 0 = (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹ * Ctop)
    (hA3last :
      let A3early := retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3
      let earlyTail : Matrix (κ' (Fin.last (M + 1))) ρ K :=
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3early C 0 (Nat.zero_le (M + 1))
      let CtopLast : Matrix ρ ρ K :=
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1 (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
      A3 (Fin.last M) = -(F3 - earlyTail) * CtopLast) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C;
    (-(suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).B = F2 0) ∧
      (suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).Ctop =
        Ctop ∧
      lowerLeftBlock
          (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).L = F3 ∧
      (∀ p : Fin (M + 1),
        transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last) =
          retainedPassiveTransformedEdge A1 F2 A3 C p) := by
  let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C
  have hA1 : ∀ p : Fin (M + 1), IsUnit (A1 p).det :=
    retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul
      (K := K) (ρ := ρ) A1 Ctop hPassiveA1 hCtop hA10
  have hB0 :
      (suffixState E (Fin.last (M + 1)) 0
        (Fin.zero_le (Fin.last (M + 1)))).B = -F2 0 := by
    simpa [E] using
      suffixState_B_retainedPassiveFixedBaseEdgeMatrix
        (K := K) (ρ := ρ) (κ := κ') A1 F2 A3 C hF2last hA1
        (0 : Fin (M + 2)) (Fin.zero_le (Fin.last (M + 1)))
  have hCtop0 :
      (suffixState E (Fin.last (M + 1)) 0
        (Fin.zero_le (Fin.last (M + 1)))).Ctop = Ctop := by
    simpa [E] using
      suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_zero_eq_target_of_A1_zero_eq
        (K := K) (ρ := ρ) (κ' := κ') A1 F2 A3 C Ctop
        hF2last hPassiveA1 hCtop hA10
  have hCtopLast :
      IsUnit
        (residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1 (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last).det := by
    let i : Fin (M + 2) := (Fin.last M).castSucc
    have hunit :
        IsUnit
          ((suffixState E (Fin.last (M + 1)) i i.le_last).Ctop).det := by
      simpa [E, i] using
        suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix
          (K := K) (ρ := ρ) (κ := κ') A1 F2 A3 C hF2last hA1 i i.le_last
    have hprod :
        (suffixState E (Fin.last (M + 1)) i i.le_last).Ctop =
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1 (Fin.last (M + 1)) i i.le_last := by
      simpa [E, i] using
        suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix
          (K := K) (ρ := ρ) (κ := κ') A1 F2 A3 C hF2last hA1 i i.le_last
    rw [hprod] at hunit
    simpa [i] using hunit
  have hTailTarget :
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3 C 0 (Nat.zero_le (M + 1)) = F3 := by
    exact
      retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq
        (K := K) (ρ := ρ) (κ' := κ') A1 A3 C F3 hCtopLast hA3last
  have hLower :
      lowerLeftBlock
          (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).L =
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3 C 0 (Nat.zero_le (M + 1)) := by
    simpa [E] using
      suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_productTailSum
        (K := K) (ρ := ρ) (κ := κ') A1 F2 A3 C hF2last hA1
  refine ⟨?_, hCtop0, ?_, ?_⟩
  · rw [hB0]
    exact neg_neg (F2 0)
  · simpa [E] using hLower.trans hTailTarget
  · intro p
    exact
      retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq
        (K := K) (ρ := ρ) (κ := κ') A1 F2 A3 C hF2last hA1 p

/-- Retained-passive fixed-base edges with solved endpoint blocks read back the
active source-left fields and every transformed-edge coordinate block. -/
theorem retainedPassiveFixedBaseEdgeMatrix_activeEndpointAndEdgeReadbacks_eq_targets
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (M + 2), Matrix ρ (κ' i) K)
    (A3 : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (Ctop : Matrix ρ ρ K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K)
    (hF2last : F2 (Fin.last (M + 1)) = 0)
    (hPassiveA1 : ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (A1 p).det)
    (hCtop : IsUnit Ctop.det)
    (hA10 :
      A1 0 = (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹ * Ctop)
    (hA3last :
      let A3early := retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3
      let earlyTail : Matrix (κ' (Fin.last (M + 1))) ρ K :=
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3early C 0 (Nat.zero_le (M + 1))
      let CtopLast : Matrix ρ ρ K :=
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1 (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
      A3 (Fin.last M) = -(F3 - earlyTail) * CtopLast) :
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C;
    (-(suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).B = F2 0) ∧
      (suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).Ctop =
        Ctop ∧
      lowerLeftBlock
          (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).L = F3 ∧
      (∀ p : Fin (M + 1),
        let T := transformedEdge E p
          (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last)
        topLeftCorner T = A1 p ∧
          upperRightBlock T = -(A1 p * F2 p.castSucc) ∧
          -((A1 p)⁻¹ * upperRightBlock T) = F2 p.castSucc ∧
          lowerLeftBlock T = A3 p ∧
          schurResidualBlock T = C p) := by
  intro E
  have hA1 : ∀ p : Fin (M + 1), IsUnit (A1 p).det :=
    retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul
      (K := K) (ρ := ρ) A1 Ctop hPassiveA1 hCtop hA10
  have hEndpoint :
      (-(suffixState E (Fin.last (M + 1)) 0
          (Fin.zero_le (Fin.last (M + 1)))).B = F2 0) ∧
        (suffixState E (Fin.last (M + 1)) 0
          (Fin.zero_le (Fin.last (M + 1)))).Ctop = Ctop ∧
        lowerLeftBlock
            (suffixState E (Fin.last (M + 1)) 0
              (Fin.zero_le (Fin.last (M + 1)))).L = F3 ∧
        (∀ p : Fin (M + 1),
          transformedEdge E p
              (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last) =
            retainedPassiveTransformedEdge A1 F2 A3 C p) := by
    simpa [E] using
      retainedPassiveFixedBaseEdgeMatrix_activeEndpointFields_eq_targets
        (K := K) (ρ := ρ) (κ' := κ') A1 F2 A3 C Ctop F3
        hF2last hPassiveA1 hCtop hA10 hA3last
  refine ⟨hEndpoint.1, hEndpoint.2.1, hEndpoint.2.2.1, ?_⟩
  intro p
  simpa [E] using
    retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks
      (K := K) (ρ := ρ) (κ := κ') A1 F2 A3 C hF2last hA1 p

/-- Solve the omitted first retained-passive top-left block from the active
source-left top block and the passive top-left tail. -/
def retainedPassiveSolvedA1
    {M : ℕ}
    (A1seed : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K) : Fin (M + 1) → Matrix ρ ρ K :=
  fun p ↦
    if p = 0 then
      (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1seed)⁻¹ * Ctop
    else
      A1seed p

@[simp]
theorem retainedPassiveSolvedA1_zero
    {M : ℕ}
    (A1seed : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K) :
    retainedPassiveSolvedA1 (K := K) (ρ := ρ) A1seed Ctop 0 =
      (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1seed)⁻¹ * Ctop := by
  simp [retainedPassiveSolvedA1]

theorem retainedPassiveSolvedA1_eq_of_ne_zero
    {M : ℕ}
    (A1seed : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K)
    {p : Fin (M + 1)} (hp : p ≠ 0) :
    retainedPassiveSolvedA1 (K := K) (ρ := ρ) A1seed Ctop p = A1seed p := by
  simp [retainedPassiveSolvedA1, hp]

/-- The passive top-left tail is unchanged by solving the first block. -/
theorem retainedPassiveA1TailAfterFirst_solvedA1
    {M : ℕ}
    (A1seed : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K) :
    retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ)
        (retainedPassiveSolvedA1 (K := K) (ρ := ρ) A1seed Ctop) =
      retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1seed := by
  let A1sol := retainedPassiveSolvedA1 (K := K) (ρ := ρ) A1seed Ctop
  let j : Fin (M + 2) := Fin.last (M + 1)
  let motive : (m : ℕ) → m ≤ M + 1 → Prop := fun m hm ↦
    1 ≤ m →
      residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1sol j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm) =
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1seed j ⟨m, Nat.lt_succ_of_le hm⟩ (Fin.val_fin_le.mpr hm)
  have hbase : motive (M + 1) le_rfl := by
    intro _hmpos
    change
      residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1sol j j le_rfl =
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1seed j j le_rfl
    simp
  have hstep : ∀ m (hms : m + 1 ≤ M + 1),
      motive (m + 1) hms → motive m (Nat.le_of_succ_le hms) := by
    intro m hms ih hmpos
    let p : Fin (M + 1) := ⟨m, Nat.lt_of_succ_le hms⟩
    have hp_ne : p ≠ 0 := by
      intro hp
      have hval : p.val = (0 : Fin (M + 1)).val := congrArg Fin.val hp
      simp [p] at hval
      omega
    have hprodSol :
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1sol j p.castSucc p.castSucc.le_last =
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
              A1sol j p.succ p.succ.le_last * A1sol p := by
      simpa [j, p] using
        residualFactorProduct_castSucc (K := K)
          (κ := fun _ : Fin (M + 2) ↦ ρ) A1sol (j := j) p p.succ.le_last
    have hprodSeed :
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1seed j p.castSucc p.castSucc.le_last =
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
              A1seed j p.succ p.succ.le_last * A1seed p := by
      simpa [j, p] using
        residualFactorProduct_castSucc (K := K)
          (κ := fun _ : Fin (M + 2) ↦ ρ) A1seed (j := j) p p.succ.le_last
    have ih' :
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1sol j p.succ p.succ.le_last =
          residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
            A1seed j p.succ p.succ.le_last := by
      have hmpos_succ : 1 ≤ m + 1 := Nat.succ_pos m
      simpa [motive, j, p] using ih hmpos_succ
    have hA1p : A1sol p = A1seed p := by
      simpa [A1sol] using
        retainedPassiveSolvedA1_eq_of_ne_zero
          (K := K) (ρ := ρ) A1seed Ctop hp_ne
    change
      residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1sol j p.castSucc p.castSucc.le_last =
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1seed j p.castSucc p.castSucc.le_last
    rw [hprodSol, hprodSeed, ih', hA1p]
  have hcanon :=
    Nat.decreasingInduction (motive := motive) hstep hbase
      (Nat.succ_le_succ (Nat.zero_le M))
  have htail := hcanon le_rfl
  simpa [retainedPassiveA1TailAfterFirst, A1sol, j, motive] using htail

/-- The solved `A1` family satisfies the endpoint equation consumed by the
fixed-base readback package. -/
theorem retainedPassiveSolvedA1_zero_eq_tail_inv_mul
    {M : ℕ}
    (A1seed : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K) :
    retainedPassiveSolvedA1 (K := K) (ρ := ρ) A1seed Ctop 0 =
      (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ)
        (retainedPassiveSolvedA1 (K := K) (ρ := ρ) A1seed Ctop))⁻¹ * Ctop := by
  rw [retainedPassiveA1TailAfterFirst_solvedA1]
  simp

theorem retainedPassiveSolvedA1_passive_det_isUnit
    {M : ℕ}
    (A1seed : Fin (M + 1) → Matrix ρ ρ K)
    (Ctop : Matrix ρ ρ K)
    (hPassive : ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (A1seed p).det) :
    ∀ p : Fin (M + 1), p ≠ 0 →
      IsUnit (retainedPassiveSolvedA1 (K := K) (ρ := ρ) A1seed Ctop p).det := by
  intro p hp
  rw [retainedPassiveSolvedA1_eq_of_ne_zero (K := K) (ρ := ρ) A1seed Ctop hp]
  exact hPassive p hp

/-- Solve the omitted final retained-passive lower-left block from the active
source-left lower-left target and the earlier-edge tail. -/
def retainedPassiveSolvedA3
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3seed : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K) :
    ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K :=
  fun p ↦
    if h : p = Fin.last M then by
      subst p
      let A3early := retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3seed
      let earlyTail : Matrix (κ' (Fin.last (M + 1))) ρ K :=
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3early C 0 (Nat.zero_le (M + 1))
      let CtopLast : Matrix ρ ρ K :=
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1 (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
      exact -(F3 - earlyTail) * CtopLast
    else
      A3seed p

@[simp]
theorem retainedPassiveSolvedA3_last
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3seed : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K) :
    retainedPassiveSolvedA3 (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3
        (Fin.last M) =
      let A3early := retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3seed
      let earlyTail : Matrix (κ' (Fin.last (M + 1))) ρ K :=
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3early C 0 (Nat.zero_le (M + 1))
      let CtopLast : Matrix ρ ρ K :=
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1 (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
      (-(F3 - earlyTail) * CtopLast) := by
  simp [retainedPassiveSolvedA3]

theorem retainedPassiveSolvedA3_eq_of_ne_last
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3seed : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K)
    {p : Fin (M + 1)} (hp : p ≠ Fin.last M) :
    retainedPassiveSolvedA3 (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3 p =
      A3seed p := by
  simp [retainedPassiveSolvedA3, hp]

theorem retainedPassiveA3WithoutLast_solvedA3
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3seed : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K) :
    retainedPassiveA3WithoutLast (K := K) (ρ := ρ)
        (retainedPassiveSolvedA3 (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3) =
      retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3seed := by
  funext p
  by_cases hp : p = Fin.last M
  · subst p
    simp
  · rw [retainedPassiveA3WithoutLast_eq_of_ne (K := K) (ρ := ρ)
        (retainedPassiveSolvedA3 (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3) hp]
    rw [retainedPassiveA3WithoutLast_eq_of_ne (K := K) (ρ := ρ) A3seed hp]
    exact
      retainedPassiveSolvedA3_eq_of_ne_last
        (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3 hp

/-- The solved `A3` family satisfies the endpoint equation consumed by the
fixed-base readback package. -/
theorem retainedPassiveSolvedA3_last_eq_target
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1 : Fin (M + 1) → Matrix ρ ρ K)
    (A3seed : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K) :
    let A3 := retainedPassiveSolvedA3 (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3
    let A3early := retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3
    let earlyTail : Matrix (κ' (Fin.last (M + 1))) ρ K :=
      retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
        A1 A3early C 0 (Nat.zero_le (M + 1))
    let CtopLast : Matrix ρ ρ K :=
      residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
        A1 (Fin.last (M + 1)) (Fin.last M).castSucc
          (Fin.last M).castSucc.le_last
    A3 (Fin.last M) = -(F3 - earlyTail) * CtopLast := by
  dsimp
  rw [retainedPassiveA3WithoutLast_solvedA3
    (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3]
  simp [retainedPassiveSolvedA3]

/-- The solved retained-passive fixed-base source family reads back the active
source-left fields and every transformed-edge coordinate block. -/
theorem retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (A1seed : Fin (M + 1) → Matrix ρ ρ K)
    (F2 : ∀ i : Fin (M + 2), Matrix ρ (κ' i) K)
    (A3seed : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K)
    (C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K)
    (Ctop : Matrix ρ ρ K)
    (F3 : Matrix (κ' (Fin.last (M + 1))) ρ K)
    (hF2last : F2 (Fin.last (M + 1)) = 0)
    (hPassiveA1 : ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (A1seed p).det)
    (hCtop : IsUnit Ctop.det) :
    let A1 := retainedPassiveSolvedA1 (K := K) (ρ := ρ) A1seed Ctop
    let A3 := retainedPassiveSolvedA3 (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3
    let E := retainedPassiveFixedBaseEdgeMatrix A1 F2 A3 C;
    (-(suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).B = F2 0) ∧
      (suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).Ctop =
        Ctop ∧
      lowerLeftBlock
          (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).L = F3 ∧
      (∀ p : Fin (M + 1),
        let T := transformedEdge E p
          (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last)
        topLeftCorner T = A1 p ∧
          upperRightBlock T = -(A1 p * F2 p.castSucc) ∧
          -((A1 p)⁻¹ * upperRightBlock T) = F2 p.castSucc ∧
          lowerLeftBlock T = A3 p ∧
          schurResidualBlock T = C p) := by
  intro A1 A3 E
  have hPassiveA1sol : ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (A1 p).det := by
    simpa [A1] using
      retainedPassiveSolvedA1_passive_det_isUnit
        (K := K) (ρ := ρ) A1seed Ctop hPassiveA1
  have hA10 :
      A1 0 = (retainedPassiveA1TailAfterFirst (K := K) (ρ := ρ) A1)⁻¹ * Ctop := by
    simpa [A1] using
      retainedPassiveSolvedA1_zero_eq_tail_inv_mul (K := K) (ρ := ρ) A1seed Ctop
  have hA3last :
      let A3early := retainedPassiveA3WithoutLast (K := K) (ρ := ρ) A3
      let earlyTail : Matrix (κ' (Fin.last (M + 1))) ρ K :=
        retainedPassiveLowerLeftProductTailSum (K := K) (ρ := ρ) (κ := κ')
          A1 A3early C 0 (Nat.zero_le (M + 1))
      let CtopLast : Matrix ρ ρ K :=
        residualFactorProduct (K := K) (κ := fun _ : Fin (M + 2) ↦ ρ)
          A1 (Fin.last (M + 1)) (Fin.last M).castSucc
            (Fin.last M).castSucc.le_last
      A3 (Fin.last M) = -(F3 - earlyTail) * CtopLast := by
    simpa [A1, A3] using
      retainedPassiveSolvedA3_last_eq_target
        (K := K) (ρ := ρ) (κ' := κ') A1 A3seed C F3
  simpa [A1, A3, E] using
    retainedPassiveFixedBaseEdgeMatrix_activeEndpointAndEdgeReadbacks_eq_targets
      (K := K) (ρ := ρ) (κ' := κ') A1 F2 A3 C Ctop F3
      hF2last hPassiveA1sol hCtop hA10 hA3last

/-- Bundled finite retained-passive coordinate data for the fixed-base source
map.  This is algebraic data only, not a topological coordinate domain. -/
structure RetainedPassiveCoordinateData
    {M : ℕ} (κ' : Fin (M + 2) → Type*) where
  A1seed : Fin (M + 1) → Matrix ρ ρ K
  F2 : ∀ i : Fin (M + 2), Matrix ρ (κ' i) K
  A3seed : ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K
  C : ∀ p : Fin (M + 1), Matrix (κ' p.succ) (κ' p.castSucc) K
  Ctop : Matrix ρ ρ K
  F3 : Matrix (κ' (Fin.last (M + 1))) ρ K

namespace RetainedPassiveCoordinateData

/-- The solved full `A1` family associated to retained-passive coordinate data. -/
def solvedA1
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    (data : RetainedPassiveCoordinateData (K := K) (ρ := ρ) κ') :
    Fin (M + 1) → Matrix ρ ρ K :=
  retainedPassiveSolvedA1 (K := K) (ρ := ρ) data.A1seed data.Ctop

/-- The solved full `A3` family associated to retained-passive coordinate data. -/
def solvedA3
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (data : RetainedPassiveCoordinateData (K := K) (ρ := ρ) κ') :
    ∀ p : Fin (M + 1), Matrix (κ' p.succ) ρ K :=
  retainedPassiveSolvedA3 (K := K) (ρ := ρ) (κ' := κ')
    (data.solvedA1) data.A3seed data.C data.F3

/-- The fixed-base edge family built from retained-passive coordinate data. -/
def edgeMatrix
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (data : RetainedPassiveCoordinateData (K := K) (ρ := ρ) κ') :
    ∀ p : Fin (M + 1), Matrix (ρ ⊕ κ' p.succ) (ρ ⊕ κ' p.castSucc) K :=
  retainedPassiveFixedBaseEdgeMatrix data.solvedA1 data.F2 data.solvedA3 data.C

/-- Bundled finite retained-passive source-map readback theorem. -/
theorem edgeMatrix_readbacks_eq_targets
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (data : RetainedPassiveCoordinateData (K := K) (ρ := ρ) κ')
    (hF2last : data.F2 (Fin.last (M + 1)) = 0)
    (hPassiveA1 :
      ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (data.A1seed p).det)
    (hCtop : IsUnit data.Ctop.det) :
    let E := data.edgeMatrix
    (-(suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).B =
        data.F2 0) ∧
      (suffixState E (Fin.last (M + 1)) 0
          (Fin.zero_le (Fin.last (M + 1)))).Ctop = data.Ctop ∧
      lowerLeftBlock
          (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).L = data.F3 ∧
      (∀ p : Fin (M + 1),
        let T := transformedEdge E p
          (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last)
        topLeftCorner T = data.solvedA1 p ∧
          upperRightBlock T = -(data.solvedA1 p * data.F2 p.castSucc) ∧
          -((data.solvedA1 p)⁻¹ * upperRightBlock T) = data.F2 p.castSucc ∧
          lowerLeftBlock T = data.solvedA3 p ∧
          schurResidualBlock T = data.C p) := by
  intro E
  simpa [edgeMatrix, solvedA1, solvedA3, E] using
    retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets
      (K := K) (ρ := ρ) (κ' := κ') data.A1seed data.F2 data.A3seed data.C
      data.Ctop data.F3 hF2last hPassiveA1 hCtop

/-- The constructed edge family reads back exactly the retained coordinate
fields, except for the two dummy endpoint seed fields. -/
theorem edgeMatrix_recoverableReadbacks_eq_targets
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (data : RetainedPassiveCoordinateData (K := K) (ρ := ρ) κ')
    (hF2last : data.F2 (Fin.last (M + 1)) = 0)
    (hPassiveA1 :
      ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (data.A1seed p).det)
    (hCtop : IsUnit data.Ctop.det) :
    let E := data.edgeMatrix
    (-(suffixState E (Fin.last (M + 1)) 0 (Fin.zero_le (Fin.last (M + 1)))).B =
        data.F2 0) ∧
      (suffixState E (Fin.last (M + 1)) 0
          (Fin.zero_le (Fin.last (M + 1)))).Ctop = data.Ctop ∧
      lowerLeftBlock
          (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).L = data.F3 ∧
      (∀ p : Fin (M + 1), p ≠ 0 →
        let T := transformedEdge E p
          (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
        topLeftCorner T = data.A1seed p) ∧
      (∀ p : Fin (M + 1),
        let T := transformedEdge E p
          (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
        -((topLeftCorner T)⁻¹ * upperRightBlock T) = data.F2 p.castSucc) ∧
      (∀ p : Fin (M + 1), p ≠ Fin.last M →
        let T := transformedEdge E p
          (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
        lowerLeftBlock T = data.A3seed p) ∧
      (∀ p : Fin (M + 1),
        let T := transformedEdge E p
          (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
        schurResidualBlock T = data.C p) := by
  intro E
  have hReadbacks :
      (-(suffixState E (Fin.last (M + 1)) 0
          (Fin.zero_le (Fin.last (M + 1)))).B = data.F2 0) ∧
        (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).Ctop = data.Ctop ∧
        lowerLeftBlock
            (suffixState E (Fin.last (M + 1)) 0
              (Fin.zero_le (Fin.last (M + 1)))).L = data.F3 ∧
        (∀ p : Fin (M + 1),
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          topLeftCorner T = data.solvedA1 p ∧
            upperRightBlock T = -(data.solvedA1 p * data.F2 p.castSucc) ∧
            -((data.solvedA1 p)⁻¹ * upperRightBlock T) = data.F2 p.castSucc ∧
            lowerLeftBlock T = data.solvedA3 p ∧
            schurResidualBlock T = data.C p) := by
    simpa [E] using
      edgeMatrix_readbacks_eq_targets
        (K := K) (ρ := ρ) data hF2last hPassiveA1 hCtop
  rcases hReadbacks with ⟨hF20, hCtopRead, hF3Read, hEdge⟩
  refine ⟨hF20, hCtopRead, hF3Read, ?_, ?_, ?_, ?_⟩
  · intro p hp
    let T := transformedEdge E p
      (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last)
    have hTop : topLeftCorner T = data.solvedA1 p := (hEdge p).1
    calc
      topLeftCorner T = data.solvedA1 p := hTop
      _ = data.A1seed p := by
        simpa [solvedA1] using
          retainedPassiveSolvedA1_eq_of_ne_zero
            (K := K) (ρ := ρ) data.A1seed data.Ctop hp
  · intro p
    let T := transformedEdge E p
      (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last)
    have hTop : topLeftCorner T = data.solvedA1 p := (hEdge p).1
    have hF2 : -((data.solvedA1 p)⁻¹ * upperRightBlock T) =
        data.F2 p.castSucc := (hEdge p).2.2.1
    change -((topLeftCorner T)⁻¹ * upperRightBlock T) = data.F2 p.castSucc
    rw [hTop]
    exact hF2
  · intro p hp
    let T := transformedEdge E p
      (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last)
    have hA3 : lowerLeftBlock T = data.solvedA3 p := (hEdge p).2.2.2.1
    calc
      lowerLeftBlock T = data.solvedA3 p := hA3
      _ = data.A3seed p := by
        simpa [solvedA3] using
          retainedPassiveSolvedA3_eq_of_ne_last
            (K := K) (ρ := ρ) (κ' := κ') data.solvedA1
            data.A3seed data.C data.F3 hp
  · intro p
    let T := transformedEdge E p
      (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last)
    exact (hEdge p).2.2.2.2

/-- Equal constructed edge families have equal recoverable retained-passive
coordinate fields; the dummy endpoint seed fields are intentionally omitted. -/
theorem edgeMatrix_recoverable_ext
    {M : ℕ} {κ' : Fin (M + 2) → Type*}
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (data data' : RetainedPassiveCoordinateData (K := K) (ρ := ρ) κ')
    (hF2last : data.F2 (Fin.last (M + 1)) = 0)
    (hF2last' : data'.F2 (Fin.last (M + 1)) = 0)
    (hPassiveA1 :
      ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (data.A1seed p).det)
    (hPassiveA1' :
      ∀ p : Fin (M + 1), p ≠ 0 → IsUnit (data'.A1seed p).det)
    (hCtop : IsUnit data.Ctop.det)
    (hCtop' : IsUnit data'.Ctop.det)
    (hE : data.edgeMatrix = data'.edgeMatrix) :
    (∀ p : Fin (M + 1), p ≠ 0 → data.A1seed p = data'.A1seed p) ∧
      data.F2 = data'.F2 ∧
      (∀ p : Fin (M + 1), p ≠ Fin.last M →
        data.A3seed p = data'.A3seed p) ∧
      data.C = data'.C ∧
      data.Ctop = data'.Ctop ∧
      data.F3 = data'.F3 := by
  let E := data.edgeMatrix
  have hRead :
      (-(suffixState E (Fin.last (M + 1)) 0
          (Fin.zero_le (Fin.last (M + 1)))).B = data.F2 0) ∧
        (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).Ctop = data.Ctop ∧
        lowerLeftBlock
            (suffixState E (Fin.last (M + 1)) 0
              (Fin.zero_le (Fin.last (M + 1)))).L = data.F3 ∧
        (∀ p : Fin (M + 1), p ≠ 0 →
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          topLeftCorner T = data.A1seed p) ∧
        (∀ p : Fin (M + 1),
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          -((topLeftCorner T)⁻¹ * upperRightBlock T) = data.F2 p.castSucc) ∧
        (∀ p : Fin (M + 1), p ≠ Fin.last M →
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          lowerLeftBlock T = data.A3seed p) ∧
        (∀ p : Fin (M + 1),
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          schurResidualBlock T = data.C p) := by
    simpa [E] using
      edgeMatrix_recoverableReadbacks_eq_targets
        (K := K) (ρ := ρ) data hF2last hPassiveA1 hCtop
  have hRead' :
      (-(suffixState E (Fin.last (M + 1)) 0
          (Fin.zero_le (Fin.last (M + 1)))).B = data'.F2 0) ∧
        (suffixState E (Fin.last (M + 1)) 0
            (Fin.zero_le (Fin.last (M + 1)))).Ctop = data'.Ctop ∧
        lowerLeftBlock
            (suffixState E (Fin.last (M + 1)) 0
              (Fin.zero_le (Fin.last (M + 1)))).L = data'.F3 ∧
        (∀ p : Fin (M + 1), p ≠ 0 →
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          topLeftCorner T = data'.A1seed p) ∧
        (∀ p : Fin (M + 1),
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          -((topLeftCorner T)⁻¹ * upperRightBlock T) = data'.F2 p.castSucc) ∧
        (∀ p : Fin (M + 1), p ≠ Fin.last M →
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          lowerLeftBlock T = data'.A3seed p) ∧
        (∀ p : Fin (M + 1),
          let T := transformedEdge E p
            (suffixState E (Fin.last (M + 1)) p.succ p.succ.le_last);
          schurResidualBlock T = data'.C p) := by
    simpa [E, hE] using
      edgeMatrix_recoverableReadbacks_eq_targets
        (K := K) (ρ := ρ) data' hF2last' hPassiveA1' hCtop'
  rcases hRead with ⟨hF20, hCtopRead, hF3Read, hA1, hF2, hA3, hC⟩
  rcases hRead' with ⟨hF20', hCtopRead', hF3Read', hA1', hF2', hA3', hC'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hA1 p hp).symm.trans (hA1' p hp)
  · apply funext
    exact (Fin.forall_iff_castSucc
      (P := fun i : Fin (M + 2) ↦ data.F2 i = data'.F2 i)).2
      ⟨hF2last.trans hF2last'.symm,
        fun p ↦ (hF2 p).symm.trans (hF2' p)⟩
  · intro p hp
    exact (hA3 p hp).symm.trans (hA3' p hp)
  · funext p
    exact (hC p).symm.trans (hC' p)
  · exact hCtopRead.symm.trans hCtopRead'
  · exact hF3Read.symm.trans hF3Read'

end RetainedPassiveCoordinateData

end RetainedPassive

end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
