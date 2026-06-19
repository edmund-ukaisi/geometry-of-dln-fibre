import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic

/-!
# Arithmetic checks for Aoyagi's blow-up exponents

This file isolates finite arithmetic from Aoyagi's blow-up section.  It does
not formalise a blow-up chart or an RLCT extraction theorem.
-/

noncomputable section

open scoped BigOperators

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

end Aoyagi
end DLN
end DLNFibre
