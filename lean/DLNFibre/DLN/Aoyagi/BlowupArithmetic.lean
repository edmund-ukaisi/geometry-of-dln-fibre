import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic

/-!
# Arithmetic checks for Aoyagi's blow-up exponents

This file isolates finite arithmetic from Aoyagi's blow-up section.  It does
not formalise a blow-up chart or an RLCT extraction theorem.
-/

noncomputable section

open scoped BigOperators
open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Aoyagi's terminal numerator expression for a vector `t`. -/
def terminalExponent (L : ℕ) (n t : ℕ → ℤ) : ℤ :=
  (n 1 - t 1) * (n 2 - t 1) +
    ∑ j ∈ Finset.range (L + 1),
      if 2 ≤ j then (t (j - 1) - t j) * (n (j + 1) - t j) else 0

/-- The Case 2 vector printed in Aoyagi's PDF: actual earlier widths, then `J`. -/
def printedCase2Vector (n : ℕ → ℤ) (S : ℕ) (J : ℤ) (i : ℕ) : ℤ :=
  if i < S then n (i + 1) else J

/-- Prefix minima of the actual widths, with source indexing beginning at `1`. -/
def prefixMin (n : ℕ → ℤ) : ℕ → ℤ
  | 0 => n 0
  | 1 => n 1
  | k + 2 => min (prefixMin n (k + 1)) (n (k + 2))

/-- The corrected Case 2 vector: prefix-minimum earlier widths, then `J`. -/
def prefixCase2Vector (n : ℕ → ℤ) (S : ℕ) (J : ℤ) (i : ℕ) : ℤ :=
  if i < S then prefixMin n (i + 1) else J

@[simp] theorem prefixMin_one (n : ℕ → ℤ) : prefixMin n 1 = n 1 := rfl

@[simp] theorem prefixMin_succ_succ (n : ℕ → ℤ) (k : ℕ) :
    prefixMin n (k + 2) = min (prefixMin n (k + 1)) (n (k + 2)) := rfl

theorem prefixMin_succ_eq_min (n : ℕ → ℤ) {j : ℕ} (hj : 1 ≤ j) :
    prefixMin n (j + 1) = min (prefixMin n j) (n (j + 1)) := by
  cases j with
  | zero => omega
  | succ j =>
      cases j with
      | zero => rfl
      | succ k => rfl

/-- The prefix-minimum step kills the corresponding terminal-exponent factor. -/
theorem prefixMin_step_factor_zero (n : ℕ → ℤ) {j : ℕ} (hj : 1 ≤ j) :
    (prefixMin n j - prefixMin n (j + 1)) *
        (n (j + 1) - prefixMin n (j + 1)) = 0 := by
  rw [prefixMin_succ_eq_min n hj]
  by_cases h : prefixMin n j ≤ n (j + 1)
  · rw [min_eq_left h]
    ring
  · rw [min_eq_right (le_of_lt (not_le.mp h))]
    ring

/-- The printed Case 2 vector evaluates to the expression with actual width `M^(S)`. -/
theorem terminalExponent_printedCase2Vector (L S : ℕ) (n : ℕ → ℤ) (J : ℤ)
    (hS : 1 ≤ S) (hSL : S ≤ L) :
    terminalExponent L n (printedCase2Vector n S J) =
      (n S - J) * (n (S + 1) - J) := by
  by_cases hS1 : S = 1
  · subst S
    have hsum :
        (∑ j ∈ Finset.range (L + 1),
          if 2 ≤ j then
            (printedCase2Vector n 1 J (j - 1) - printedCase2Vector n 1 J j) *
              (n (j + 1) - printedCase2Vector n 1 J j)
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_cases h2 : 2 ≤ j
      · have hj1 : ¬ j < 1 := by omega
        have hjm1 : ¬ j - 1 < 1 := by omega
        simp [h2, printedCase2Vector, hj1, hjm1]
      · simp [h2]
    rw [terminalExponent, hsum]
    simp [printedCase2Vector]
  · have hS2 : 2 ≤ S := by omega
    have hbase :
        (n 1 - printedCase2Vector n S J 1) *
            (n 2 - printedCase2Vector n S J 1) = 0 := by
      have h1S : 1 < S := by omega
      simp [printedCase2Vector, h1S]
    have hsum :
        (∑ j ∈ Finset.range (L + 1),
          if 2 ≤ j then
            (printedCase2Vector n S J (j - 1) - printedCase2Vector n S J j) *
              (n (j + 1) - printedCase2Vector n S J j)
          else 0) = (n S - J) * (n (S + 1) - J) := by
      calc
        (∑ j ∈ Finset.range (L + 1),
          if 2 ≤ j then
            (printedCase2Vector n S J (j - 1) - printedCase2Vector n S J j) *
              (n (j + 1) - printedCase2Vector n S J j)
          else 0)
            =
              (if 2 ≤ S then
                (printedCase2Vector n S J (S - 1) - printedCase2Vector n S J S) *
                  (n (S + 1) - printedCase2Vector n S J S)
              else 0) := by
                refine Finset.sum_eq_single S ?_ ?_
                · intro j hjmem hjne
                  by_cases h2 : 2 ≤ j
                  · by_cases hjS : j < S
                    · have hpred : j - 1 < S := by omega
                      have hm : j - 1 + 1 = j := by omega
                      simp [h2, printedCase2Vector, hjS, hpred, hm]
                    · have hSj : S < j := by omega
                      have hjnot : ¬ j < S := by omega
                      have hprednot : ¬ j - 1 < S := by omega
                      simp [h2, printedCase2Vector, hjnot, hprednot]
                  · simp [h2]
                · intro hnot
                  exact absurd (by simp [hSL]) hnot
        _ = (n S - J) * (n (S + 1) - J) := by
          have hm : S - 1 + 1 = S := by omega
          have hpred : S - 1 < S := by omega
          simp [hS2, printedCase2Vector, hpred, hm]
    rw [terminalExponent, hbase, hsum]
    ring

/-- The corrected prefix-minimum Case 2 vector evaluates to Aoyagi's printed update. -/
theorem terminalExponent_prefixCase2Vector (L S : ℕ) (n : ℕ → ℤ) (J : ℤ)
    (hS : 1 ≤ S) (hSL : S ≤ L) :
    terminalExponent L n (prefixCase2Vector n S J) =
      (prefixMin n S - J) * (n (S + 1) - J) := by
  by_cases hS1 : S = 1
  · subst S
    have hsum :
        (∑ j ∈ Finset.range (L + 1),
          if 2 ≤ j then
            (prefixCase2Vector n 1 J (j - 1) - prefixCase2Vector n 1 J j) *
              (n (j + 1) - prefixCase2Vector n 1 J j)
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_cases h2 : 2 ≤ j
      · have hj1 : ¬ j < 1 := by omega
        have hjm1 : ¬ j - 1 < 1 := by omega
        simp [h2, prefixCase2Vector, hj1, hjm1]
      · simp [h2]
    rw [terminalExponent, hsum]
    simp [prefixCase2Vector]
  · have hS2 : 2 ≤ S := by omega
    have hbase :
        (n 1 - prefixCase2Vector n S J 1) *
            (n 2 - prefixCase2Vector n S J 1) = 0 := by
      have h1S : 1 < S := by omega
      simpa [prefixCase2Vector, h1S] using prefixMin_step_factor_zero n (j := 1) (by omega)
    have hsum :
        (∑ j ∈ Finset.range (L + 1),
          if 2 ≤ j then
            (prefixCase2Vector n S J (j - 1) - prefixCase2Vector n S J j) *
              (n (j + 1) - prefixCase2Vector n S J j)
          else 0) = (prefixMin n S - J) * (n (S + 1) - J) := by
      calc
        (∑ j ∈ Finset.range (L + 1),
          if 2 ≤ j then
            (prefixCase2Vector n S J (j - 1) - prefixCase2Vector n S J j) *
              (n (j + 1) - prefixCase2Vector n S J j)
          else 0)
            =
              (if 2 ≤ S then
                (prefixCase2Vector n S J (S - 1) - prefixCase2Vector n S J S) *
                  (n (S + 1) - prefixCase2Vector n S J S)
              else 0) := by
                refine Finset.sum_eq_single S ?_ ?_
                · intro j hjmem hjne
                  by_cases h2 : 2 ≤ j
                  · by_cases hjS : j < S
                    · have hpred : j - 1 < S := by omega
                      have hm : j - 1 + 1 = j := by omega
                      have hfactor := prefixMin_step_factor_zero n (j := j) (by omega : 1 ≤ j)
                      simpa [h2, prefixCase2Vector, hjS, hpred, hm] using hfactor
                    · have hSj : S < j := by omega
                      have hjnot : ¬ j < S := by omega
                      have hprednot : ¬ j - 1 < S := by omega
                      simp [h2, prefixCase2Vector, hjnot, hprednot]
                  · simp [h2]
                · intro hnot
                  exact absurd (by simp [hSL]) hnot
        _ = (prefixMin n S - J) * (n (S + 1) - J) := by
          have hm : S - 1 + 1 = S := by omega
          have hpred : S - 1 < S := by omega
          simp [hS2, prefixCase2Vector, hpred, hm]
    rw [terminalExponent, hbase, hsum]
    ring

section MonomialRecurrence

variable {α : Type*} [CommMonoid α]

/-- A monomial recurrence `b_{i+1}=step_i*b_i` with `b_0=1`. -/
def monomialRec (step : ℕ → α) : ℕ → α
  | 0 => 1
  | k + 1 => step k * monomialRec step k

/-- The explicit product of recurrence factors between two levels. -/
def monomialTail (step : ℕ → α) (a : ℕ) : ℕ → α
  | 0 => 1
  | k + 1 => step (a + k) * monomialTail step a k

@[simp] theorem monomialRec_zero (step : ℕ → α) : monomialRec step 0 = 1 := rfl

@[simp] theorem monomialRec_succ (step : ℕ → α) (k : ℕ) :
    monomialRec step (k + 1) = step k * monomialRec step k := rfl

@[simp] theorem monomialTail_zero (step : ℕ → α) (a : ℕ) :
    monomialTail step a 0 = 1 := rfl

@[simp] theorem monomialTail_succ (step : ℕ → α) (a k : ℕ) :
    monomialTail step a (k + 1) = step (a + k) * monomialTail step a k := rfl

/-- A later recurrence term is the earlier one times the tail product. -/
theorem monomialRec_add_eq_tail_mul (step : ℕ → α) (a k : ℕ) :
    monomialRec step (a + k) = monomialTail step a k * monomialRec step a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, monomialRec_succ, ih, monomialTail_succ]
      ac_rfl

/-- Every later monomial recurrence term is divisible by every earlier one. -/
theorem monomialRec_dvd_of_le (step : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    monomialRec step a ∣ monomialRec step b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨monomialTail step a k, ?_⟩
  rw [monomialRec_add_eq_tail_mul step a k]
  ac_rfl

/-- The divisibility needed by `P`: `b_{J+1}` divides every later `b_i`. -/
theorem monomialRec_pivot_dvd (step : ℕ → α) {J i : ℕ} (h : J + 1 ≤ i) :
    monomialRec step (J + 1) ∣ monomialRec step i :=
  monomialRec_dvd_of_le step h

/-- Multiplying both monomials by the pivot variable preserves divisibility. -/
theorem mul_left_dvd_mul_left_of_dvd {a b u : α} (h : a ∣ b) :
    u * a ∣ u * b := by
  rcases h with ⟨c, rfl⟩
  exact ⟨c, by ac_rfl⟩

/-- The post-pivot divisibility for the common update `b'_i = u*b_i`. -/
theorem pivotMul_monomialRec_dvd_of_le (step : ℕ → α) (u : α) {a b : ℕ}
    (h : a ≤ b) :
    u * monomialRec step a ∣ u * monomialRec step b :=
  mul_left_dvd_mul_left_of_dvd (monomialRec_dvd_of_le step h)

end MonomialRecurrence

section RowOperationScalars

variable {R : Type*} [CommRing R]

/-- Scalar algebra for the weighted row operation used in the pivot chart. -/
theorem weightedPivotRow_scalar (b0 bi q di0 d0j dij : R)
    (hbi : bi = q * b0) :
    -(q * di0) * (b0 * d0j) + bi * dij = bi * (dij - di0 * d0j) := by
  rw [hbi]
  ring

/-- The pivot row operation clears the first-column entry below the pivot. -/
theorem weightedPivotRow_firstColumn_zero (b0 bi q di0 : R)
    (hbi : bi = q * b0) :
    -(q * di0) * b0 + bi * di0 = 0 := by
  rw [hbi]
  ring

/-- If the post-`Q` top row has zero off the pivot, the lower-right entry is unchanged. -/
theorem weightedPivotRow_topRowZero (b0 bi q di0 dij : R)
    (hbi : bi = q * b0) :
    -(q * di0) * (b0 * 0) + bi * dij = bi * dij := by
  rw [hbi]
  ring

end RowOperationScalars

section RowOperationBlocks

variable {R ρ κ : Type*} [CommRing R] [Fintype ρ] [DecidableEq ρ]

/-- The lower-unitriangular row-operation matrix used after the pivot row has been normalised. -/
def weightedPivotBlockRowOp (q x : ρ → R) : Matrix (Unit ⊕ ρ) (Unit ⊕ ρ) R :=
  fromBlocks 1 0 (fun i _ ↦ -(q i * x i)) 1

/-- The post-`Q` pivot block: top row `(1,0,...,0)` and lower-left column `x`. -/
def weightedPivotBlockMatrix (x : ρ → R) (D : Matrix ρ κ R) :
    Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R :=
  fromBlocks 1 0 (fun i _ ↦ x i) D

/-- The same pivot block after the first column has been cleared below the pivot. -/
def weightedPivotClearedBlock (D : Matrix ρ κ R) : Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R :=
  fromBlocks 1 0 0 D

/-- Diagonal weights split into the pivot weight and the lower-row weights. -/
def weightedPivotDiagonal (b0 : R) (b : ρ → R) : Matrix (Unit ⊕ ρ) (Unit ⊕ ρ) R :=
  fromBlocks (fun _ _ ↦ b0) 0 0 (diagonal b)

set_option linter.flexible false in
/-- The normalised `P` row operation clears the first column below the pivot. -/
theorem weightedPivotBlockRowOp_mul_diagonal_mul
    (b0 : R) (b q x : ρ → R) (D : Matrix ρ κ R)
    (h : ∀ i, b i = q i * b0) :
    weightedPivotBlockRowOp q x * weightedPivotDiagonal b0 b * weightedPivotBlockMatrix x D =
      weightedPivotDiagonal b0 b * weightedPivotClearedBlock D := by
  rw [Matrix.mul_assoc]
  ext r c
  rcases r with (_ | i)
  · rcases c with (_ | j)
    · simp [weightedPivotBlockRowOp, weightedPivotDiagonal, weightedPivotBlockMatrix,
        weightedPivotClearedBlock, Matrix.fromBlocks_multiply]
    · simp [weightedPivotBlockRowOp, weightedPivotDiagonal, weightedPivotBlockMatrix,
        weightedPivotClearedBlock, Matrix.fromBlocks_multiply]
  · rcases c with (_ | j)
    · simp [weightedPivotBlockRowOp, weightedPivotDiagonal, weightedPivotBlockMatrix,
        weightedPivotClearedBlock, Matrix.fromBlocks_multiply, Matrix.mul_apply,
        Matrix.one_apply]
      have hdiag : (∑ x_1, diagonal b i x_1 * x x_1) = b i * x i := by
        simpa [dotProduct] using (diagonal_dotProduct (v := b) (w := x) i)
      rw [hdiag, h i]
      ring
    · simp [weightedPivotBlockRowOp, weightedPivotDiagonal, weightedPivotBlockMatrix,
        weightedPivotClearedBlock, Matrix.fromBlocks_multiply, h]

end RowOperationBlocks

section ColumnOperationBlocks

variable {R ρ κ τ : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]

/-- The pre-`Q` pivot block, with top row `[1 y]`. -/
def pivotPreQBlock (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R) :
    Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R :=
  fromBlocks 1 y x D

/-- The elementary right column operation that clears the pivot row off the pivot. -/
def pivotQ (y : Matrix Unit κ R) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R :=
  fromBlocks 1 (-y) 0 1

/-- The inverse elementary column operation. -/
def pivotQinv (y : Matrix Unit κ R) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R :=
  fromBlocks 1 y 0 1

/-- The `Q`-normalised pivot block. -/
def pivotPostQBlock (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R) :
    Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R :=
  fromBlocks 1 0 x (D - x * y)

/-- Right multiplication by `Q` clears the pivot row away from the pivot. -/
theorem pivotPreQBlock_mul_pivotQ
    (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R) :
    pivotPreQBlock x y D * pivotQ y = pivotPostQBlock x y D := by
  ext r c
  rcases r with (_ | i)
  · rcases c with (_ | j)
    · simp [pivotPreQBlock, pivotQ, pivotPostQBlock, Matrix.fromBlocks_multiply]
    · simp [pivotPreQBlock, pivotQ, pivotPostQBlock, Matrix.fromBlocks_multiply]
  · rcases c with (_ | j)
    · simp [pivotPreQBlock, pivotQ, pivotPostQBlock, Matrix.fromBlocks_multiply]
    · simp [pivotPreQBlock, pivotQ, pivotPostQBlock, Matrix.fromBlocks_multiply,
        sub_eq_add_neg, add_comm]

/-- The displayed inverse really is a right inverse for `Q`. -/
theorem pivotQ_mul_pivotQinv (y : Matrix Unit κ R) :
    pivotQ y * pivotQinv y = 1 := by
  rw [← fromBlocks_one (l := Unit) (m := κ)]
  simp [pivotQ, pivotQinv, Matrix.fromBlocks_multiply]

/-- The displayed inverse really is a left inverse for `Q`. -/
theorem pivotQinv_mul_pivotQ (y : Matrix Unit κ R) :
    pivotQinv y * pivotQ y = 1 := by
  rw [← fromBlocks_one (l := Unit) (m := κ)]
  simp [pivotQ, pivotQinv, Matrix.fromBlocks_multiply]

/-- Transforming the next factor by `Q⁻¹` preserves the local product. -/
theorem pivotPreQBlock_mul_eq_postQ_mul_Qinv_mul
    (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R)
    (C : Matrix (Unit ⊕ κ) τ R) :
    pivotPreQBlock x y D * C = pivotPostQBlock x y D * (pivotQinv y * C) := by
  symm
  calc
    pivotPostQBlock x y D * (pivotQinv y * C)
        = (pivotPreQBlock x y D * pivotQ y) * (pivotQinv y * C) := by
            rw [pivotPreQBlock_mul_pivotQ]
    _ = pivotPreQBlock x y D * (pivotQ y * (pivotQinv y * C)) := by
            rw [Matrix.mul_assoc]
    _ = pivotPreQBlock x y D * ((pivotQ y * pivotQinv y) * C) := by
            rw [← Matrix.mul_assoc (pivotQ y) (pivotQinv y) C]
    _ = pivotPreQBlock x y D * C := by
            rw [pivotQ_mul_pivotQinv]
            simp

omit [Fintype κ] [DecidableEq κ] in
/-- The `Q`-normalised block is the same block shape used by the `P` row-operation API. -/
theorem pivotPostQBlock_eq_weightedPivotBlockMatrix
    (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R) :
    pivotPostQBlock x y D =
      weightedPivotBlockMatrix (fun i ↦ x i ()) (D - x * y) := by
  ext r c
  rcases r with (_ | i)
  · rcases c with (_ | j)
    · simp [pivotPostQBlock, weightedPivotBlockMatrix]
    · simp [pivotPostQBlock, weightedPivotBlockMatrix]
  · rcases c with (_ | j)
    · simp [pivotPostQBlock, weightedPivotBlockMatrix]
    · simp [pivotPostQBlock, weightedPivotBlockMatrix]

omit [Fintype κ] [DecidableEq κ] in
/-- After `Q` normalisation, the weighted `P` row operation clears the pivot column. -/
theorem weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock
    [Fintype ρ] [DecidableEq ρ]
    (b0 : R) (b q : ρ → R)
    (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R)
    (h : ∀ i, b i = q i * b0) :
    weightedPivotBlockRowOp q (fun i ↦ x i ()) * weightedPivotDiagonal b0 b *
        pivotPostQBlock x y D =
      weightedPivotDiagonal b0 b * weightedPivotClearedBlock (D - x * y) := by
  rw [pivotPostQBlock_eq_weightedPivotBlockMatrix]
  exact weightedPivotBlockRowOp_mul_diagonal_mul b0 b q (fun i ↦ x i ()) (D - x * y) h

/-- The local normalised `Q`-then-`P` pivot identity. -/
theorem weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ
    [Fintype ρ] [DecidableEq ρ]
    (b0 : R) (b q : ρ → R)
    (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R)
    (h : ∀ i, b i = q i * b0) :
    weightedPivotBlockRowOp q (fun i ↦ x i ()) * weightedPivotDiagonal b0 b *
        (pivotPreQBlock x y D * pivotQ y) =
      weightedPivotDiagonal b0 b * weightedPivotClearedBlock (D - x * y) := by
  rw [pivotPreQBlock_mul_pivotQ]
  exact weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock b0 b q x y D h

/-- An algebraic pivot-step corollary with the following factor multiplied by `Q⁻¹`. -/
theorem weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul
    [Fintype ρ] [DecidableEq ρ]
    (b0 : R) (b q : ρ → R)
    (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R)
    (C : Matrix (Unit ⊕ κ) τ R) (h : ∀ i, b i = q i * b0) :
    (weightedPivotBlockRowOp q (fun i ↦ x i ()) * weightedPivotDiagonal b0 b *
        pivotPreQBlock x y D) * C =
      (weightedPivotDiagonal b0 b * weightedPivotClearedBlock (D - x * y)) *
        (pivotQinv y * C) := by
  calc
    (weightedPivotBlockRowOp q (fun i ↦ x i ()) * weightedPivotDiagonal b0 b *
          pivotPreQBlock x y D) * C
        =
          (weightedPivotBlockRowOp q (fun i ↦ x i ()) * weightedPivotDiagonal b0 b) *
            (pivotPreQBlock x y D * C) := by
            rw [Matrix.mul_assoc]
    _ =
          (weightedPivotBlockRowOp q (fun i ↦ x i ()) * weightedPivotDiagonal b0 b) *
            (pivotPostQBlock x y D * (pivotQinv y * C)) := by
            rw [pivotPreQBlock_mul_eq_postQ_mul_Qinv_mul]
    _ =
          (weightedPivotBlockRowOp q (fun i ↦ x i ()) * weightedPivotDiagonal b0 b *
            pivotPostQBlock x y D) * (pivotQinv y * C) := by
            rw [← Matrix.mul_assoc]
    _ =
          (weightedPivotDiagonal b0 b * weightedPivotClearedBlock (D - x * y)) *
            (pivotQinv y * C) := by
            rw [weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock b0 b q x y D h]

end ColumnOperationBlocks

end Aoyagi
end DLN
end DLNFibre
