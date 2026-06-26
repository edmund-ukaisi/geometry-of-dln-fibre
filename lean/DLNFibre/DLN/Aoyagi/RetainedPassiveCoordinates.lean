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

end RetainedPassive

end ChartLocalSuffixState
end Aoyagi
end DLN
end DLNFibre
