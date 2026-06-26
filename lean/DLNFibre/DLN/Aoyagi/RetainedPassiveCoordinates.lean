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
