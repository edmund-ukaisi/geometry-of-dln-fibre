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

section LabelRanges

/-- Natural widths viewed as integer widths for terminal-exponent arithmetic. -/
def widthZ (n : ℕ → ℕ) (i : ℕ) : ℤ := n i

/-- Prefix minima for natural-number actual widths. -/
def prefixMinNat (n : ℕ → ℕ) : ℕ → ℕ
  | 0 => n 0
  | 1 => n 1
  | k + 2 => min (prefixMinNat n (k + 1)) (n (k + 2))

@[simp] theorem prefixMinNat_one (n : ℕ → ℕ) : prefixMinNat n 1 = n 1 := rfl

@[simp] theorem prefixMinNat_succ_succ (n : ℕ → ℕ) (k : ℕ) :
    prefixMinNat n (k + 2) = min (prefixMinNat n (k + 1)) (n (k + 2)) := rfl

theorem prefixMinNat_succ_eq_min (n : ℕ → ℕ) {j : ℕ} (hj : 1 ≤ j) :
    prefixMinNat n (j + 1) = min (prefixMinNat n j) (n (j + 1)) := by
  cases j with
  | zero => omega
  | succ j =>
      cases j with
      | zero => rfl
      | succ k => rfl

/-- Prefix minima can only decrease as the prefix grows. -/
theorem prefixMinNat_succ_le (n : ℕ → ℕ) {j : ℕ} (hj : 1 ≤ j) :
    prefixMinNat n (j + 1) ≤ prefixMinNat n j := by
  rw [prefixMinNat_succ_eq_min n hj]
  exact min_le_left _ _

/-- Prefix minima are antitone in the positive prefix index. -/
theorem prefixMinNat_antitone (n : ℕ → ℕ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    prefixMinNat n b ≤ prefixMinNat n a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ]
      exact le_trans (prefixMinNat_succ_le n (by omega : 1 ≤ a + k)) (ih (by omega))

/-- Natural prefix minima agree with integer prefix minima after casting widths. -/
theorem prefixMinNat_cast (n : ℕ → ℕ) (i : ℕ) :
    (prefixMinNat n i : ℤ) = prefixMin (widthZ n) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      cases i with
      | zero => rfl
      | succ k =>
          rw [prefixMinNat_succ_succ, prefixMin_succ_succ, ← ih]
          exact Nat.cast_min (prefixMinNat n (k + 1)) (n (k + 2))

/-- The prefix minimum at a positive index is bounded by that actual width. -/
theorem prefixMinNat_le_width (n : ℕ → ℕ) {j : ℕ} (hj : 1 ≤ j) :
    prefixMinNat n j ≤ n j := by
  cases j with
  | zero => omega
  | succ j =>
      cases j with
      | zero => rfl
      | succ k => simp [prefixMinNat]

/-- A source label range using the actual layer width `n_(s+1)`. -/
def actualWidthLabel (L : ℕ) (n : ℕ → ℕ) (s k : ℕ) : Prop :=
  1 ≤ s ∧ s ≤ L ∧ 1 ≤ k ∧ k ≤ n (s + 1)

/-- The narrower label range obtained by incorrectly using the prefix minimum. -/
def prefixWidthLabel (L : ℕ) (n : ℕ → ℕ) (s k : ℕ) : Prop :=
  1 ≤ s ∧ s ≤ L ∧ 1 ≤ k ∧ k ≤ prefixMinNat n (s + 1)

/-- Labels whose exceptional variables have been introduced by state `(S,J)`. -/
def introducedLabel (L : ℕ) (n : ℕ → ℕ) (S J s k : ℕ) : Prop :=
  actualWidthLabel L n s k ∧ (s < S ∨ s = S ∧ k ≤ J)

/-- Prefix-minimum labels are actual-width labels, but not conversely in general. -/
theorem actualWidthLabel_of_prefixWidthLabel {L : ℕ} {n : ℕ → ℕ} {s k : ℕ}
    (h : prefixWidthLabel L n s k) : actualWidthLabel L n s k := by
  rcases h with ⟨hs0, hsL, hk0, hk⟩
  exact ⟨hs0, hsL, hk0, le_trans hk (prefixMinNat_le_width n (by omega : 1 ≤ s + 1))⟩

/-- Introduced labels are always source-valid actual-width labels. -/
theorem actualWidthLabel_of_introducedLabel {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ}
    (h : introducedLabel L n S J s k) : actualWidthLabel L n s k :=
  h.1

/-- A label from an earlier layer is introduced at state `(S,J)`. -/
theorem introducedLabel_of_lt_stage {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ}
    (hlabel : actualWidthLabel L n s k) (hs : s < S) :
    introducedLabel L n S J s k :=
  ⟨hlabel, Or.inl hs⟩

/-- A label in the current layer is introduced exactly up to the processed index `J`. -/
theorem introducedLabel_of_eq_stage_le {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ}
    (hlabel : actualWidthLabel L n s k) (hs : s = S) (hk : k ≤ J) :
    introducedLabel L n S J s k :=
  ⟨hlabel, Or.inr ⟨hs, hk⟩⟩

/-- Increasing `J` can only add introduced labels in the current layer. -/
theorem introducedLabel_mono_J {L : ℕ} {n : ℕ → ℕ} {S J J' s k : ℕ}
    (hJJ : J ≤ J') (h : introducedLabel L n S J s k) :
    introducedLabel L n S J' s k := by
  rcases h with ⟨hlabel, hs | ⟨hs, hk⟩⟩
  · exact ⟨hlabel, Or.inl hs⟩
  · exact ⟨hlabel, Or.inr ⟨hs, le_trans hk hJJ⟩⟩

/-- If the actual width is larger than the prefix minimum, prefix labels undercount. -/
theorem actualWidthLabel_not_prefixWidthLabel_of_prefixMinNat_lt_width
    (L : ℕ) (n : ℕ → ℕ) {s : ℕ}
    (hs0 : 1 ≤ s) (hsL : s ≤ L) (h : prefixMinNat n (s + 1) < n (s + 1)) :
    actualWidthLabel L n s (prefixMinNat n (s + 1) + 1) ∧
      ¬ prefixWidthLabel L n s (prefixMinNat n (s + 1) + 1) := by
  constructor
  · exact ⟨hs0, hsL, by omega, by omega⟩
  · intro hprefix
    exact (by omega : ¬ prefixMinNat n (s + 1) + 1 ≤ prefixMinNat n (s + 1))
      hprefix.2.2.2

/-- The new pivot label `(S,J+1)` is valid against the actual source width. -/
theorem actualWidthLabel_case2_new (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hJ : J + 1 ≤ n (S + 1)) :
    actualWidthLabel L n S (J + 1) :=
  ⟨hS, hSL, by omega, hJ⟩

/-- Under the continuation bound, the new pivot label also lies in the prefix range. -/
theorem prefixWidthLabel_case2_new (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hJ : J + 1 ≤ prefixMinNat n (S + 1)) :
    prefixWidthLabel L n S (J + 1) :=
  ⟨hS, hSL, by omega, hJ⟩

/-- Before the pivot advance, the would-be new label `(S,J+1)` is not introduced. -/
theorem not_introducedLabel_case2_new_before (L : ℕ) (n : ℕ → ℕ) (S J : ℕ) :
    ¬ introducedLabel L n S J S (J + 1) := by
  intro h
  rcases h.2 with hlt | ⟨heq, hk⟩
  · omega
  · omega

/-- After the pivot advance, the new label `(S,J+1)` is introduced. -/
theorem introducedLabel_case2_new_after (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hJ : J + 1 ≤ n (S + 1)) :
    introducedLabel L n S (J + 1) S (J + 1) :=
  ⟨actualWidthLabel_case2_new L n hS hSL hJ, Or.inr ⟨rfl, le_rfl⟩⟩

/-- The source continuation bound is a stronger way to introduce `(S,J+1)`. -/
theorem introducedLabel_case2_new_after_of_prefixBound (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hJ : J + 1 ≤ prefixMinNat n (S + 1)) :
    introducedLabel L n S (J + 1) S (J + 1) :=
  introducedLabel_case2_new_after L n hS hSL
    (le_trans hJ (prefixMinNat_le_width n (by omega : 1 ≤ S + 1)))

/-- The corrected Case 2 pivot vector, using prefix minima before `S`. -/
def correctedCase2PivotVector (n : ℕ → ℕ) (S J : ℕ) : ℕ → ℤ :=
  prefixCase2Vector (widthZ n) S (J : ℤ)

@[simp] theorem correctedCase2PivotVector_apply (n : ℕ → ℕ) (S J i : ℕ) :
    correctedCase2PivotVector n S J i =
      if i < S then (prefixMinNat n (i + 1) : ℤ) else (J : ℤ) := by
  by_cases hi : i < S
  · simp [correctedCase2PivotVector, prefixCase2Vector, hi, prefixMinNat_cast]
  · simp [correctedCase2PivotVector, prefixCase2Vector, hi]

/-- Before `S`, the corrected Case 2 vector is the prefix minimum. -/
theorem correctedCase2PivotVector_eq_prefix_of_lt
    (n : ℕ → ℕ) {S J i : ℕ} (hi : i < S) :
    correctedCase2PivotVector n S J i = (prefixMinNat n (i + 1) : ℤ) := by
  simp [hi]

/-- From `S` onward, the corrected Case 2 vector is `J`. -/
theorem correctedCase2PivotVector_eq_J_of_le
    (n : ℕ → ℕ) {S J i : ℕ} (hi : S ≤ i) :
    correctedCase2PivotVector n S J i = (J : ℤ) := by
  simp [not_lt_of_ge hi]

@[simp] theorem correctedCase2PivotVector_self (n : ℕ → ℕ) (S J : ℕ) :
    correctedCase2PivotVector n S J S = (J : ℤ) :=
  correctedCase2PivotVector_eq_J_of_le n le_rfl

/-- Under the state bound `J ≤ mu_S`, every corrected Case 2 component is at least `J`. -/
theorem le_correctedCase2PivotVector_of_le_prefixMinNat
    (n : ℕ → ℕ) {S J : ℕ} (hJ : J ≤ prefixMinNat n S) (i : ℕ) :
    (J : ℤ) ≤ correctedCase2PivotVector n S J i := by
  by_cases hi : i < S
  · rw [correctedCase2PivotVector_eq_prefix_of_lt n hi]
    have hmono : prefixMinNat n S ≤ prefixMinNat n (i + 1) :=
      prefixMinNat_antitone n (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ S)
    exact_mod_cast le_trans hJ hmono
  · rw [correctedCase2PivotVector_eq_J_of_le n (le_of_not_gt hi)]

/-- The corrected Case 2 vector has minimum value `J` in the finite bookkeeping sense. -/
theorem correctedCase2PivotVector_min_certificate
    (n : ℕ → ℕ) {S J : ℕ} (hJ : J ≤ prefixMinNat n S) :
    (∀ i, (J : ℤ) ≤ correctedCase2PivotVector n S J i) ∧
      correctedCase2PivotVector n S J S = (J : ℤ) :=
  ⟨le_correctedCase2PivotVector_of_le_prefixMinNat n hJ,
    correctedCase2PivotVector_self n S J⟩

/-- Over the source component range, the corrected Case 2 vector has least value `J`. -/
theorem correctedCase2PivotVector_isLeast_valueSet_Icc
    (n : ℕ → ℕ) {L S J : ℕ} (hS : 1 ≤ S) (hSL : S ≤ L)
    (hJ : J ≤ prefixMinNat n S) :
    IsLeast
      {v : ℤ | ∃ i, i ∈ Finset.Icc 1 L ∧ correctedCase2PivotVector n S J i = v}
      (J : ℤ) := by
  constructor
  · exact ⟨S, by simp [Finset.mem_Icc, hS, hSL], correctedCase2PivotVector_self n S J⟩
  · intro v hv
    rcases hv with ⟨i, hi, rfl⟩
    exact le_correctedCase2PivotVector_of_le_prefixMinNat n hJ i

end LabelRanges

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

/-- The corrected Case 2 vector has the prefix-minimum terminal exponent. -/
theorem terminalExponent_correctedCase2PivotVector
    (L S : ℕ) (n : ℕ → ℕ) (J : ℕ) (hS : 1 ≤ S) (hSL : S ≤ L) :
    terminalExponent L (widthZ n) (correctedCase2PivotVector n S J) =
      ((prefixMinNat n S : ℤ) - (J : ℤ)) *
        ((n (S + 1) : ℤ) - (J : ℤ)) := by
  rw [correctedCase2PivotVector, terminalExponent_prefixCase2Vector L S (widthZ n)
    (J : ℤ) hS hSL, ← prefixMinNat_cast]
  rfl

/-- Finite certificate assigned only to the corrected Case 2 new pivot label. -/
structure CorrectedCase2NewLabelCertificate (L : ℕ) (n : ℕ → ℕ) (S J : ℕ) : Prop where
  introduced : introducedLabel L n S (J + 1) S (J + 1)
  terminalExponent_eq :
    terminalExponent L (widthZ n) (correctedCase2PivotVector n S J) =
      ((prefixMinNat n S : ℤ) - (J : ℤ)) * ((n (S + 1) : ℤ) - (J : ℤ))
  least_value :
    IsLeast
      {v : ℤ | ∃ i, i ∈ Finset.Icc 1 L ∧ correctedCase2PivotVector n S J i = v}
      (J : ℤ)

/-- Actual label validity plus the state bound give the corrected new-label certificate. -/
theorem correctedCase2NewLabelCertificate_of_actualBound_of_stateBound
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hJactual : J + 1 ≤ n (S + 1))
    (hJstate : J ≤ prefixMinNat n S) :
    CorrectedCase2NewLabelCertificate L n S J where
  introduced := introducedLabel_case2_new_after L n hS hSL hJactual
  terminalExponent_eq := terminalExponent_correctedCase2PivotVector L S n J hS hSL
  least_value := correctedCase2PivotVector_isLeast_valueSet_Icc n hS hSL hJstate

/-- The source continuation bound is a sufficient way to get the corrected certificate. -/
theorem correctedCase2NewLabelCertificate_of_prefixBound
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hJcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    CorrectedCase2NewLabelCertificate L n S J := by
  refine correctedCase2NewLabelCertificate_of_actualBound_of_stateBound L n hS hSL
    (le_trans hJcont (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))) ?_
  exact le_trans (by omega : J ≤ J + 1) (le_trans hJcont (prefixMinNat_succ_le n hS))

/-- A finite terminal-exponent and minimum certificate for one introduced label. -/
structure LabelExponentCertificate
    (L : ℕ) (n : ℕ → ℕ) (S J s k : ℕ)
    (t : ℕ → ℤ) (numerator leastValue : ℤ) : Prop where
  introduced : introducedLabel L n S J s k
  terminalExponent_eq : terminalExponent L (widthZ n) t = numerator
  least_value :
    IsLeast {v : ℤ | ∃ i, i ∈ Finset.Icc 1 L ∧ t i = v} leastValue

/-- The corrected Case 2 one-label certificate is a generic label certificate. -/
theorem CorrectedCase2NewLabelCertificate.labelExponentCertificate
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (h : CorrectedCase2NewLabelCertificate L n S J) :
    LabelExponentCertificate L n S (J + 1) S (J + 1)
      (correctedCase2PivotVector n S J)
      (((prefixMinNat n S : ℤ) - (J : ℤ)) * ((n (S + 1) : ℤ) - (J : ℤ)))
      (J : ℤ) where
  introduced := h.introduced
  terminalExponent_eq := h.terminalExponent_eq
  least_value := h.least_value

/-- Any label newly present after advancing `J` must have indices `(S,J+1)`. -/
theorem introducedLabel_succ_cases
    {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ}
    (h : introducedLabel L n S (J + 1) s k) :
    introducedLabel L n S J s k ∨ (s = S ∧ k = J + 1) := by
  rcases h with ⟨hlabel, hs | ⟨hs, hk⟩⟩
  · exact Or.inl ⟨hlabel, Or.inl hs⟩
  · by_cases hkle : k ≤ J
    · exact Or.inl ⟨hlabel, Or.inr ⟨hs, hkle⟩⟩
    · exact Or.inr ⟨hs, by omega⟩

/-- One `J`-advance changes the introduced domain only at the next current-layer label. -/
theorem introducedLabel_succ_iff
    (L : ℕ) (n : ℕ → ℕ) (S J s k : ℕ) :
    introducedLabel L n S (J + 1) s k ↔
      introducedLabel L n S J s k ∨
        actualWidthLabel L n s k ∧ s = S ∧ k = J + 1 := by
  constructor
  · intro h
    rcases introducedLabel_succ_cases h with hOld | ⟨hs, hk⟩
    · exact Or.inl hOld
    · exact Or.inr ⟨h.1, hs, hk⟩
  · intro h
    rcases h with hOld | ⟨hlabel, hs, hk⟩
    · exact introducedLabel_mono_J (by omega : J ≤ J + 1) hOld
    · exact ⟨hlabel, Or.inr ⟨hs, by omega⟩⟩

/-- Terminal-exponent/minimum certificates for all labels introduced at a state. -/
structure IntroducedLabelExponentCertificates
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (t : ℕ → ℕ → ℕ → ℤ) (numerator leastValue : ℕ → ℕ → ℤ) : Prop where
  certificate :
    ∀ {s k}, introducedLabel L n S J s k →
      LabelExponentCertificate L n S J s k (t s k) (numerator s k) (leastValue s k)

/-- Same-domain bookkeeping: replace one introduced label certificate and keep all
other introduced labels unchanged. -/
theorem IntroducedLabelExponentCertificates.updateSelected
    {L : ℕ} {n : ℕ → ℕ} {S J s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hnew :
      LabelExponentCertificate L n S J s0 k0 (t' s0 k0)
        (numerator' s0 k0) (leastValue' s0 k0))
    (ht_old :
      ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
        t' s k = t s k)
    (hn_old :
      ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
        numerator' s k = numerator s k)
    (hl_old :
      ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
        leastValue' s k = leastValue s k) :
    IntroducedLabelExponentCertificates L n S J t' numerator' leastValue' where
  certificate := by
    intro s k hintro
    by_cases hsame : s = s0 ∧ k = k0
    · rcases hsame with ⟨rfl, rfl⟩
      exact hnew
    · have hc := hcert.certificate hintro
      refine
        { introduced := hintro
          terminalExponent_eq := ?_
          least_value := ?_ }
      · rw [ht_old hintro hsame, hn_old hintro hsame]
        exact hc.terminalExponent_eq
      · rw [ht_old hintro hsame, hl_old hintro hsame]
        exact hc.least_value

/-- Replace the vector assignment at one selected label, leaving all other labels unchanged. -/
def updateSelectedLabelVector
    (s0 k0 : ℕ) (new : ℕ → ℤ) (old : ℕ → ℕ → ℕ → ℤ) (s k i : ℕ) : ℤ :=
  if s = s0 ∧ k = k0 then new i else old s k i

/-- Replace a scalar label assignment at one selected label, leaving all other labels unchanged. -/
def updateSelectedLabelScalar
    (s0 k0 : ℕ) (new : ℤ) (old : ℕ → ℕ → ℤ) (s k : ℕ) : ℤ :=
  if s = s0 ∧ k = k0 then new else old s k

@[simp] theorem updateSelectedLabelVector_selected
    (s0 k0 : ℕ) (new : ℕ → ℤ) (old : ℕ → ℕ → ℕ → ℤ) (i : ℕ) :
    updateSelectedLabelVector s0 k0 new old s0 k0 i = new i := by
  simp [updateSelectedLabelVector]

theorem updateSelectedLabelVector_of_ne
    {s0 k0 s k : ℕ} (new : ℕ → ℤ) (old : ℕ → ℕ → ℕ → ℤ) (i : ℕ)
    (hne : ¬ (s = s0 ∧ k = k0)) :
    updateSelectedLabelVector s0 k0 new old s k i = old s k i := by
  simp [updateSelectedLabelVector, hne]

@[simp] theorem updateSelectedLabelScalar_selected
    (s0 k0 : ℕ) (new : ℤ) (old : ℕ → ℕ → ℤ) :
    updateSelectedLabelScalar s0 k0 new old s0 k0 = new := by
  simp [updateSelectedLabelScalar]

theorem updateSelectedLabelScalar_of_ne
    {s0 k0 s k : ℕ} (new : ℤ) (old : ℕ → ℕ → ℤ)
    (hne : ¬ (s = s0 ∧ k = k0)) :
    updateSelectedLabelScalar s0 k0 new old s k = old s k := by
  simp [updateSelectedLabelScalar, hne]

/-- Domain-extension bookkeeping only: add one current-layer label certificate. -/
theorem IntroducedLabelExponentCertificates.extendDomain_succ_current
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hnew :
      LabelExponentCertificate L n S (J + 1) S (J + 1)
        (t' S (J + 1)) (numerator' S (J + 1)) (leastValue' S (J + 1)))
    (ht_old : ∀ {s k}, introducedLabel L n S J s k → t' s k = t s k)
    (hn_old : ∀ {s k}, introducedLabel L n S J s k → numerator' s k = numerator s k)
    (hl_old : ∀ {s k}, introducedLabel L n S J s k → leastValue' s k = leastValue s k) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' where
  certificate := by
    intro s k hintro
    rcases introducedLabel_succ_cases hintro with hOld | ⟨rfl, rfl⟩
    · have hc := hcert.certificate hOld
      refine
        { introduced := hintro
          terminalExponent_eq := ?_
          least_value := ?_ }
      · rw [ht_old hOld, hn_old hOld]
        exact hc.terminalExponent_eq
      · rw [ht_old hOld, hl_old hOld]
        exact hc.least_value
    · exact hnew

/-- Domain-extension bookkeeping using the corrected Case 2 new-label certificate. -/
theorem IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_bounds
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hJactual : J + 1 ≤ n (S + 1))
    (hJstate : J ≤ prefixMinNat n S)
    (ht_old : ∀ {s k}, introducedLabel L n S J s k → t' s k = t s k)
    (hn_old : ∀ {s k}, introducedLabel L n S J s k → numerator' s k = numerator s k)
    (hl_old : ∀ {s k}, introducedLabel L n S J s k → leastValue' s k = leastValue s k)
    (ht_new : t' S (J + 1) = correctedCase2PivotVector n S J)
    (hn_new :
      numerator' S (J + 1) =
        ((prefixMinNat n S : ℤ) - (J : ℤ)) * ((n (S + 1) : ℤ) - (J : ℤ)))
    (hl_new : leastValue' S (J + 1) = (J : ℤ)) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' := by
  refine hcert.extendDomain_succ_current ?_ ht_old hn_old hl_old
  rw [ht_new, hn_new, hl_new]
  exact
    (correctedCase2NewLabelCertificate_of_actualBound_of_stateBound
      L n hS hSL hJactual hJstate).labelExponentCertificate

/-- The continuation bound is a sufficient hypothesis for the corrected domain extension. -/
theorem IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_prefixBound
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hJcont : J + 1 ≤ prefixMinNat n (S + 1))
    (ht_old : ∀ {s k}, introducedLabel L n S J s k → t' s k = t s k)
    (hn_old : ∀ {s k}, introducedLabel L n S J s k → numerator' s k = numerator s k)
    (hl_old : ∀ {s k}, introducedLabel L n S J s k → leastValue' s k = leastValue s k)
    (ht_new : t' S (J + 1) = correctedCase2PivotVector n S J)
    (hn_new :
      numerator' S (J + 1) =
        ((prefixMinNat n S : ℤ) - (J : ℤ)) * ((n (S + 1) : ℤ) - (J : ℤ)))
    (hl_new : leastValue' S (J + 1) = (J : ℤ)) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' := by
  refine hcert.extendDomain_succ_current ?_ ht_old hn_old hl_old
  rw [ht_new, hn_new, hl_new]
  exact
    (correctedCase2NewLabelCertificate_of_prefixBound
      L n hS hSL hJcont).labelExponentCertificate

/-- Row indices in the residual block blown up in corrected Case 2. -/
def case2ResidualBlockRows (n : ℕ → ℕ) (S J : ℕ) : Finset ℕ :=
  Finset.Icc (J + 1) (prefixMinNat n S)

/-- Column indices in the residual block blown up in corrected Case 2. -/
def case2ResidualBlockCols (n : ℕ → ℕ) (S J : ℕ) : Finset ℕ :=
  Finset.Icc (J + 1) (n (S + 1))

/-- Finite row index type for the corrected Case 2 residual block. -/
abbrev Case2ResidualRowIndex (n : ℕ → ℕ) (S J : ℕ) :=
  (case2ResidualBlockRows n S J : Type)

/-- Finite column index type for the corrected Case 2 residual block. -/
abbrev Case2ResidualColIndex (n : ℕ → ℕ) (S J : ℕ) :=
  (case2ResidualBlockCols n S J : Type)

/-- Candidate selected entries in the Case 2 residual-block center, not a chart cover proof. -/
def case2ResidualBlockPivotEntries (n : ℕ → ℕ) (S J : ℕ) : Finset (ℕ × ℕ) :=
  (case2ResidualBlockRows n S J).product (case2ResidualBlockCols n S J)

@[simp] theorem mem_case2ResidualBlockRows (n : ℕ → ℕ) (S J i : ℕ) :
    i ∈ case2ResidualBlockRows n S J ↔ J + 1 ≤ i ∧ i ≤ prefixMinNat n S := by
  simp [case2ResidualBlockRows, Finset.mem_Icc]

@[simp] theorem mem_case2ResidualBlockCols (n : ℕ → ℕ) (S J j : ℕ) :
    j ∈ case2ResidualBlockCols n S J ↔ J + 1 ≤ j ∧ j ≤ n (S + 1) := by
  simp [case2ResidualBlockCols, Finset.mem_Icc]

/-- Membership in the finite set of Case 2 residual-block candidate pivot entries. -/
theorem mem_case2ResidualBlockPivotEntries_iff (n : ℕ → ℕ) (S J i j : ℕ) :
    (i, j) ∈ case2ResidualBlockPivotEntries n S J ↔
      J + 1 ≤ i ∧ i ≤ prefixMinNat n S ∧ J + 1 ≤ j ∧ j ≤ n (S + 1) := by
  simp [case2ResidualBlockPivotEntries, and_assoc]

/-- Aoyagi's displayed pivot entry is one candidate selected entry under continuation. -/
theorem case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    (J + 1, J + 1) ∈ case2ResidualBlockPivotEntries n S J := by
  rw [mem_case2ResidualBlockPivotEntries_iff]
  refine ⟨le_rfl, ?_, le_rfl, ?_⟩
  · exact le_trans hcont (prefixMinNat_succ_le n hS)
  · exact le_trans hcont (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))

/-- The displayed Case 2 pivot row `J+1`, as an element of the residual-row index type. -/
def case2DisplayedPivotRow
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    Case2ResidualRowIndex n S J :=
  ⟨J + 1, by
    rw [mem_case2ResidualBlockRows]
    exact ⟨le_rfl, le_trans hcont (prefixMinNat_succ_le n hS)⟩⟩

/-- The displayed Case 2 pivot column `J+1`, as an element of the residual-column index type. -/
def case2DisplayedPivotCol
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    Case2ResidualColIndex n S J :=
  ⟨J + 1, by
    rw [mem_case2ResidualBlockCols]
    exact ⟨le_rfl,
      le_trans hcont (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))⟩⟩

/-- Case 1 center generator symbols after externally choosing the old exceptional variable.
The `Unit` branch does not encode the old label, its validity, level, minimality, or
comparability; the right branch records a row-strip entry. -/
abbrev Case1CenterGenerator := Unit ⊕ (ℕ × ℕ)

/-- Row indices in the Case 1 row strip. -/
def case1StripRows (J J1 : ℕ) : Finset ℕ :=
  Finset.Icc (J + 1) (J + J1)

/-- Column indices in the Case 1 row strip, using actual active width, not prefix minimum. -/
def case1StripCols (n : ℕ → ℕ) (S J : ℕ) : Finset ℕ :=
  Finset.Icc (J + 1) (n (S + 1))

/-- Residual block entries appearing in the Case 1 row-strip center. -/
def case1StripEntries (n : ℕ → ℕ) (S J J1 : ℕ) : Finset (ℕ × ℕ) :=
  (case1StripRows J J1).product (case1StripCols n S J)

/-- Finite Case 1 center generators after fixing the chosen old exceptional variable.
This does not encode Case 1 hypotheses, chart coverage, regularity, exponent updates, or
termination. -/
def case1CenterGenerators (n : ℕ → ℕ) (S J J1 : ℕ) :
    Finset Case1CenterGenerator :=
  {(Sum.inl () : Case1CenterGenerator)} ∪
    (case1StripEntries n S J J1).image (fun p ↦ (Sum.inr p : Case1CenterGenerator))

@[simp] theorem mem_case1StripRows (J J1 i : ℕ) :
    i ∈ case1StripRows J J1 ↔ J + 1 ≤ i ∧ i ≤ J + J1 := by
  simp [case1StripRows, Finset.mem_Icc]

@[simp] theorem mem_case1StripCols (n : ℕ → ℕ) (S J j : ℕ) :
    j ∈ case1StripCols n S J ↔ J + 1 ≤ j ∧ j ≤ n (S + 1) := by
  simp [case1StripCols, Finset.mem_Icc]

/-- Membership in the finite Case 1 row-strip entry set. -/
theorem mem_case1StripEntries_iff (n : ℕ → ℕ) (S J J1 i j : ℕ) :
    (i, j) ∈ case1StripEntries n S J J1 ↔
      J + 1 ≤ i ∧ i ≤ J + J1 ∧ J + 1 ≤ j ∧ j ≤ n (S + 1) := by
  simp [case1StripEntries, and_assoc]

/-- Finite row-set containment under `J+J1 <= mu_S`; not a chart or transition theorem. -/
theorem case1StripRows_subset_case2ResidualBlockRows
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hrow : J + J1 ≤ prefixMinNat n S) :
    case1StripRows J J1 ⊆ case2ResidualBlockRows n S J := by
  intro i hi
  rw [mem_case1StripRows] at hi
  rw [mem_case2ResidualBlockRows]
  exact ⟨hi.1, le_trans hi.2 hrow⟩

/-- Case 1 row-strip columns use the same actual-width range as the residual block. -/
theorem case1StripCols_eq_case2ResidualBlockCols
    (n : ℕ → ℕ) (S J : ℕ) :
    case1StripCols n S J = case2ResidualBlockCols n S J :=
  rfl

/-- Finite entry-set containment under `J+J1 <= mu_S`; not chart coverage. -/
theorem case1StripEntries_subset_case2ResidualBlockPivotEntries
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hrow : J + J1 ≤ prefixMinNat n S) :
    case1StripEntries n S J J1 ⊆ case2ResidualBlockPivotEntries n S J := by
  intro p hp
  rcases p with ⟨i, j⟩
  rw [mem_case1StripEntries_iff] at hp
  rw [mem_case2ResidualBlockPivotEntries_iff]
  exact ⟨hp.1, le_trans hp.2.1 hrow, hp.2.2.1, hp.2.2.2⟩

/-- Displayed-pivot residual-block membership under entry bounds; not a transition theorem. -/
theorem case1_displayedPivot_mem_residualBlockPivotEntries_of_bounds
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hrow : J + J1 ≤ prefixMinNat n S)
    (hcol : J + 1 ≤ n (S + 1)) :
    (J + 1, J + 1) ∈ case2ResidualBlockPivotEntries n S J := by
  rw [mem_case2ResidualBlockPivotEntries_iff]
  exact ⟨le_rfl, le_trans (by omega : J + 1 ≤ J + J1) hrow, le_rfl, hcol⟩

/-- Componentwise comparison on the finite source component range `1..L`. -/
def componentwiseLEOn (L : ℕ) (t u : ℕ → ℤ) : Prop :=
  ∀ i, i ∈ Finset.Icc 1 L → t i ≤ u i

/-- Case 1 first-jump and selected-label hypotheses, as finite bookkeeping only.

The `level` field is a natural-number source index.  Bridging it to the
integer-valued `leastValue` fields in exponent certificates is a separate
integration obligation.  This structure does not construct a blow-up chart,
prove chart coverage, update exponents, or prove a transition invariant. -/
structure Case1FirstJumpHypotheses
    (L : ℕ) (n : ℕ → ℕ) (S J J1 s k : ℕ)
    (level : ℕ → ℕ → ℕ) (vector : ℕ → ℕ → ℕ → ℤ) : Prop where
  positive : 1 ≤ J1
  jumpBeforeEnd : J + J1 < prefixMinNat n S
  selectedIntroduced : introducedLabel L n S J s k
  selectedLevel : level s k = J + J1
  gap :
    ∀ {s' k'}, introducedLabel L n S J s' k' →
      ¬ (J + 1 ≤ level s' k' ∧ level s' k' < J + J1)
  minimal :
    ∀ {s' k'}, introducedLabel L n S J s' k' → level s' k' = J + J1 →
      componentwiseLEOn L (vector s k) (vector s' k')

/-- The strict Case 1 first-jump bound implies the row-strip bound. -/
theorem Case1FirstJumpHypotheses.rowBound
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector) :
    J + J1 ≤ prefixMinNat n S :=
  le_of_lt h.jumpBeforeEnd

/-- The selected Case 1 level is strictly after the current pivot level. -/
theorem Case1FirstJumpHypotheses.lt_selectedLevel
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector) :
    J < level s k := by
  rw [h.selectedLevel]
  have hpos : 0 < J1 := h.positive
  omega

/-- The selected Case 1 source level, cast to the integer convention used by certificates. -/
theorem Case1FirstJumpHypotheses.selectedLevel_int
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector) :
    (level s k : ℤ) = (J + J1 : ℤ) := by
  exact_mod_cast h.selectedLevel

/-- The selected Case 1 label is not in the forbidden first-jump gap. -/
theorem Case1FirstJumpHypotheses.not_selected_in_gap
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector) :
    ¬ (J + 1 ≤ level s k ∧ level s k < J + J1) :=
  h.gap h.selectedIntroduced

/-- The selected label is componentwise minimal among labels at its own level. -/
theorem Case1FirstJumpHypotheses.selected_componentwiseLE_self
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector) :
    componentwiseLEOn L (vector s k) (vector s k) :=
  h.minimal h.selectedIntroduced h.selectedLevel

/-- The Case 1 first-jump row bound gives row-strip containment. -/
theorem Case1FirstJumpHypotheses.stripRows_subset_residualBlockRows
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector) :
    case1StripRows J J1 ⊆ case2ResidualBlockRows n S J :=
  case1StripRows_subset_case2ResidualBlockRows n S h.rowBound

/-- The Case 1 first-jump row bound gives row-strip entry containment. -/
theorem Case1FirstJumpHypotheses.stripEntries_subset_residualBlockEntries
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector) :
    case1StripEntries n S J J1 ⊆ case2ResidualBlockPivotEntries n S J :=
  case1StripEntries_subset_case2ResidualBlockPivotEntries n S h.rowBound

/-- The chosen old exceptional variable is a Case 1 center generator. -/
theorem case1_selectedOld_mem_center (n : ℕ → ℕ) (S J J1 : ℕ) :
    (Sum.inl () : Case1CenterGenerator) ∈ case1CenterGenerators n S J J1 := by
  simp [case1CenterGenerators]

/-- Every row-strip entry is a Case 1 center generator. -/
theorem case1_stripEntry_mem_center
    {n : ℕ → ℕ} {S J J1 : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case1StripEntries n S J J1) :
    (Sum.inr p : Case1CenterGenerator) ∈ case1CenterGenerators n S J J1 := by
  simp [case1CenterGenerators, hp]

/-- Aoyagi's displayed Case 1 pivot entry belongs to the finite center under entry bounds.
This does not assert the row strip is source-valid in the active residual block. -/
theorem case1_displayedPivot_mem_center_of_bounds
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1)) :
    (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) ∈
      case1CenterGenerators n S J J1 :=
  case1_stripEntry_mem_center (by
    rw [mem_case1StripEntries_iff]
    exact ⟨le_rfl, by omega, le_rfl, hcol⟩)

/-- The Case 1 first-jump hypotheses imply displayed-pivot center membership once the
source column bound is supplied. -/
theorem Case1FirstJumpHypotheses.displayedPivot_mem_center_of_colBound
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector)
    (hcol : J + 1 ≤ n (S + 1)) :
    (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) ∈
      case1CenterGenerators n S J J1 :=
  case1_displayedPivot_mem_center_of_bounds n S h.positive hcol

/-- The Case 1 first-jump hypotheses imply displayed-pivot residual-block membership once the
source column bound is supplied. -/
theorem Case1FirstJumpHypotheses.displayedPivot_mem_residualBlockPivotEntries_of_colBound
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector)
    (hcol : J + 1 ≤ n (S + 1)) :
    (J + 1, J + 1) ∈ case2ResidualBlockPivotEntries n S J :=
  case1_displayedPivot_mem_residualBlockPivotEntries_of_bounds n S
    h.positive h.rowBound hcol

/-- A Case 1 row-strip entry is a residual-block entry under the first-jump row bound. -/
theorem Case1FirstJumpHypotheses.stripEntry_mem_residualBlockPivotEntries
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector)
    {p : ℕ × ℕ} (hp : p ∈ case1StripEntries n S J J1) :
    p ∈ case2ResidualBlockPivotEntries n S J :=
  h.stripEntries_subset_residualBlockEntries hp

section SelectedEntryChart

variable {ι α : Type*} [DecidableEq ι] [Monoid α]

/-- Algebraic substitution pattern for one selected generator of a finite center:
the selected generator is sent to `u`, and every other generator is sent to
`u * residual i`. This is only finite algebra; it does not construct a blow-up
chart or prove chart coverage, regularity, transition formulas, or Jacobian facts. -/
def selectedEntryChartMap (pivot : ι) (u : α) (residual : ι → α) (i : ι) : α :=
  u * if i = pivot then 1 else residual i

/-- The normalised selected-entry chart coordinate: the pivot is `1`, all other
center generators are residual coordinates. -/
def selectedEntryNormalizedMap (pivot : ι) (residual : ι → α) (i : ι) : α :=
  if i = pivot then 1 else residual i

@[simp] theorem selectedEntryChartMap_pivot
    (pivot : ι) (u : α) (residual : ι → α) :
    selectedEntryChartMap pivot u residual pivot = u := by
  simp [selectedEntryChartMap]

@[simp] theorem selectedEntryNormalizedMap_pivot
    (pivot : ι) (residual : ι → α) :
    selectedEntryNormalizedMap pivot residual pivot = 1 := by
  simp [selectedEntryNormalizedMap]

theorem selectedEntryChartMap_of_ne
    {pivot i : ι} (u : α) (residual : ι → α) (hi : i ≠ pivot) :
    selectedEntryChartMap pivot u residual i = u * residual i := by
  simp [selectedEntryChartMap, hi]

theorem selectedEntryNormalizedMap_of_ne
    {pivot i : ι} (residual : ι → α) (hi : i ≠ pivot) :
    selectedEntryNormalizedMap pivot residual i = residual i := by
  simp [selectedEntryNormalizedMap, hi]

/-- The selected-entry substitution is the selected variable times the normalised chart. -/
theorem selectedEntryChartMap_eq_mul_normalized
    (pivot : ι) (u : α) (residual : ι → α) (i : ι) :
    selectedEntryChartMap pivot u residual i =
      u * selectedEntryNormalizedMap pivot residual i :=
  rfl

/-- Every transformed center generator is divisible by the selected pivot variable. -/
theorem selectedEntryChartMap_pivot_dvd
    (pivot : ι) (u : α) (residual : ι → α) (i : ι) :
    u ∣ selectedEntryChartMap pivot u residual i :=
  ⟨if i = pivot then 1 else residual i, rfl⟩

/-- If the selected entry belongs to a finite center, its pivot value occurs in the value set. -/
theorem selectedEntryChartMap_pivot_mem_valueSet
    {center : Finset ι} {pivot : ι} (hpivot : pivot ∈ center)
    (u : α) (residual : ι → α) :
    u ∈ {v : α | ∃ i, i ∈ center ∧ selectedEntryChartMap pivot u residual i = v} :=
  ⟨pivot, hpivot, by simp⟩

end SelectedEntryChart

section SelectedEntrySubstitutionMatrix

variable {ι κ α : Type*} [DecidableEq ι] [DecidableEq κ] [Monoid α]

/-- Normalised matrix form of a selected-entry substitution at a chosen matrix pivot. -/
def selectedEntryNormalizedMatrix
    (rowPivot : ι) (colPivot : κ) (residual : ι → κ → α) :
    Matrix ι κ α :=
  fun i j ↦
    selectedEntryNormalizedMap (rowPivot, colPivot)
      (fun p : ι × κ ↦ residual p.1 p.2) (i, j)

/-- Matrix-valued selected-entry substitution before factoring out the selected variable. -/
def selectedEntrySubstitutionMatrix
    (rowPivot : ι) (colPivot : κ) (u : α) (residual : ι → κ → α) :
    Matrix ι κ α :=
  fun i j ↦
    selectedEntryChartMap (rowPivot, colPivot) u
      (fun p : ι × κ ↦ residual p.1 p.2) (i, j)

@[simp] theorem selectedEntryNormalizedMatrix_pivot
    (rowPivot : ι) (colPivot : κ) (residual : ι → κ → α) :
    selectedEntryNormalizedMatrix rowPivot colPivot residual rowPivot colPivot = 1 := by
  simp [selectedEntryNormalizedMatrix]

@[simp] theorem selectedEntrySubstitutionMatrix_pivot
    (rowPivot : ι) (colPivot : κ) (u : α) (residual : ι → κ → α) :
    selectedEntrySubstitutionMatrix rowPivot colPivot u residual rowPivot colPivot = u := by
  simp [selectedEntrySubstitutionMatrix]

theorem selectedEntryNormalizedMatrix_of_ne
    {rowPivot : ι} {colPivot : κ} {i : ι} {j : κ}
    (residual : ι → κ → α) (hij : (i, j) ≠ (rowPivot, colPivot)) :
    selectedEntryNormalizedMatrix rowPivot colPivot residual i j = residual i j := by
  exact selectedEntryNormalizedMap_of_ne _ hij

/-- Matrix-valued selected-entry substitution factors as the selected variable times the
normalised selected-entry matrix. -/
theorem selectedEntrySubstitutionMatrix_eq_mul_normalized
    (rowPivot : ι) (colPivot : κ) (u : α) (residual : ι → κ → α) :
    selectedEntrySubstitutionMatrix rowPivot colPivot u residual =
      fun i j ↦ u * selectedEntryNormalizedMatrix rowPivot colPivot residual i j :=
  rfl

end SelectedEntrySubstitutionMatrix

/-- In the Case 2 residual-block center, the displayed selected-entry chart has value `u`
at the displayed pivot. This is only finite selected-entry bookkeeping. -/
theorem case2_displayedPivot_selectedEntryChartMap_value_mem
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {α : Type*} [Monoid α] (u : α) (residual : ℕ × ℕ → α) :
    u ∈
      {v : α | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        selectedEntryChartMap (J + 1, J + 1) u residual p = v} :=
  selectedEntryChartMap_pivot_mem_valueSet
    (case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont) u residual

/-- In a Case 2 residual-block center, any selected entry chart has value `u` at
the selected entry. This is finite selected-entry bookkeeping, not chart coverage. -/
theorem case2_selectedEntryChartMap_value_mem_of_mem
    {n : ℕ → ℕ} {S J : ℕ} {pivot : ℕ × ℕ}
    (hpivot : pivot ∈ case2ResidualBlockPivotEntries n S J)
    {α : Type*} [Monoid α] (u : α) (residual : ℕ × ℕ → α) :
    u ∈
      {v : α | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        selectedEntryChartMap pivot u residual p = v} :=
  selectedEntryChartMap_pivot_mem_valueSet hpivot u residual

/-- In a Case 2 residual-block selected-entry chart, every transformed center
entry is divisible by the selected variable. -/
theorem case2_selectedEntryChartMap_center_dvd_of_mem
    {n : ℕ → ℕ} {S J : ℕ} {pivot : ℕ × ℕ}
    (_hpivot : pivot ∈ case2ResidualBlockPivotEntries n S J)
    {α : Type*} [Monoid α] (u : α) (residual : ℕ × ℕ → α) :
    ∀ p, p ∈ case2ResidualBlockPivotEntries n S J →
    u ∣ selectedEntryChartMap pivot u residual p :=
  fun p _ ↦ selectedEntryChartMap_pivot_dvd pivot u residual p

/-- In the Case 1 selected-old-variable chart, the selected generator has value `u`. -/
theorem case1_selectedOld_selectedEntryChartMap_value_mem
    (n : ℕ → ℕ) (S J J1 : ℕ)
    {α : Type*} [Monoid α] (u : α) (residual : Case1CenterGenerator → α) :
    u ∈
      {v : α | ∃ g, g ∈ case1CenterGenerators n S J J1 ∧
        selectedEntryChartMap (Sum.inl () : Case1CenterGenerator) u residual g = v} :=
  selectedEntryChartMap_pivot_mem_valueSet
    (case1_selectedOld_mem_center n S J J1) u residual

/-- In the displayed Case 1 pivot-entry chart, the displayed strip entry has value `u`. -/
theorem case1_displayedPivot_selectedEntryChartMap_value_mem
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1))
    {α : Type*} [Monoid α] (u : α) (residual : Case1CenterGenerator → α) :
    u ∈
      {v : α | ∃ g, g ∈ case1CenterGenerators n S J J1 ∧
        selectedEntryChartMap (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)
          u residual g = v} :=
  selectedEntryChartMap_pivot_mem_valueSet
    (case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol) u residual

/-- In a Case 1 center, any selected generator chart has value `u` at the
selected generator. This is finite selected-entry bookkeeping, not chart coverage. -/
theorem case1_selectedEntryChartMap_value_mem_of_mem
    {n : ℕ → ℕ} {S J J1 : ℕ} {pivot : Case1CenterGenerator}
    (hpivot : pivot ∈ case1CenterGenerators n S J J1)
    {α : Type*} [Monoid α] (u : α) (residual : Case1CenterGenerator → α) :
    u ∈
      {v : α | ∃ g, g ∈ case1CenterGenerators n S J J1 ∧
        selectedEntryChartMap pivot u residual g = v} :=
  selectedEntryChartMap_pivot_mem_valueSet hpivot u residual

/-- In a Case 1 selected-entry chart, every transformed center generator is
divisible by the selected variable. -/
theorem case1_selectedEntryChartMap_center_dvd_of_mem
    {n : ℕ → ℕ} {S J J1 : ℕ} {pivot : Case1CenterGenerator}
    (_hpivot : pivot ∈ case1CenterGenerators n S J J1)
    {α : Type*} [Monoid α] (u : α) (residual : Case1CenterGenerator → α) :
    ∀ g, g ∈ case1CenterGenerators n S J J1 →
    u ∣ selectedEntryChartMap pivot u residual g :=
  fun g _ ↦ selectedEntryChartMap_pivot_dvd pivot u residual g

/-- Lower the vector tail from stage `S` onward to the pivot level `J`. -/
def lowerTailVector (T : ℕ → ℤ) (S : ℕ) (J : ℤ) (i : ℕ) : ℤ :=
  if i < S then T i else J

/-- Before `S`, lowering the tail leaves the vector unchanged. -/
theorem lowerTailVector_eq_of_lt {T : ℕ → ℤ} {S i : ℕ} {J : ℤ} (hi : i < S) :
    lowerTailVector T S J i = T i := by
  simp [lowerTailVector, hi]

/-- From `S` onward, the lowered tail is constant `J`. -/
theorem lowerTailVector_eq_of_le {T : ℕ → ℤ} {S i : ℕ} {J : ℤ} (hi : S ≤ i) :
    lowerTailVector T S J i = J := by
  simp [lowerTailVector, not_lt_of_ge hi]

@[simp] theorem lowerTailVector_self (T : ℕ → ℤ) (S : ℕ) (J : ℤ) :
    lowerTailVector T S J S = J :=
  lowerTailVector_eq_of_le le_rfl

/-- Lowering the tail preserves a lower bound by the new tail value. -/
theorem le_lowerTailVector_of_le
    {T : ℕ → ℤ} {S : ℕ} {J : ℤ} (hT : ∀ i, J ≤ T i) (i : ℕ) :
    J ≤ lowerTailVector T S J i := by
  by_cases hi : i < S
  · rw [lowerTailVector_eq_of_lt hi]
    exact hT i
  · rw [lowerTailVector_eq_of_le (le_of_not_gt hi)]

/-- On the finite source range, the lowered tail has least value `J`. -/
theorem lowerTailVector_isLeast_valueSet_Icc
    {L S : ℕ} {T : ℕ → ℤ} {J : ℤ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hT : ∀ i, J ≤ T i) :
    IsLeast {v : ℤ | ∃ i, i ∈ Finset.Icc 1 L ∧ lowerTailVector T S J i = v} J := by
  constructor
  · exact ⟨S, by simp [Finset.mem_Icc, hS, hSL], lowerTailVector_self T S J⟩
  · intro v hv
    rcases hv with ⟨i, hi, rfl⟩
    exact le_lowerTailVector_of_le hT i

/-- The flat-tail hypothesis needed by the Case 1 tail-lowering arithmetic. -/
structure FlatTailFromPred (L S : ℕ) (T : ℕ → ℤ) (h : ℤ) : Prop where
  pred : T (S - 1) = h
  tail : ∀ i, S ≤ i → i ≤ L → T i = h

/-- Lowering a flat tail gives the Case 1 terminal-exponent increment. -/
theorem terminalExponent_lowerTailVector_of_flatFromPred
    (L S : ℕ) (n T : ℕ → ℤ) (h J : ℤ)
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (hpred : T (S - 1) = h)
    (htail : ∀ i, S ≤ i → i ≤ L → T i = h) :
    terminalExponent L n (lowerTailVector T S J) =
      terminalExponent L n T + (h - J) * (n (S + 1) - J) := by
  let f : ℕ → ℤ :=
    fun j ↦
      if 2 ≤ j then (T (j - 1) - T j) * (n (j + 1) - T j) else 0
  let g : ℕ → ℤ :=
    fun j ↦
      if 2 ≤ j then
        (lowerTailVector T S J (j - 1) - lowerTailVector T S J j) *
          (n (j + 1) - lowerTailVector T S J j)
      else 0
  have hbase :
      (n 1 - lowerTailVector T S J 1) * (n 2 - lowerTailVector T S J 1) =
        (n 1 - T 1) * (n 2 - T 1) := by
    simp [lowerTailVector, (by omega : 1 < S)]
  have hdiff :
      (∑ j ∈ Finset.range (L + 1), (g j - f j)) =
        g S - f S := by
    refine Finset.sum_eq_single
      (s := Finset.range (L + 1)) (a := S) (f := fun j : ℕ ↦ g j - f j) ?_ ?_
    · intro j hjmem hjne
      by_cases h2 : 2 ≤ j
      · by_cases hjS : j < S
        · have hpredlt : j - 1 < S := by omega
          simp [f, g, h2, lowerTailVector, hjS, hpredlt]
        · have hSj : S < j := by omega
          have hprednot : ¬ j - 1 < S := by omega
          have hjnot : ¬ j < S := by omega
          have hjLt : j < L + 1 := Finset.mem_range.mp hjmem
          have hjL : j ≤ L := by omega
          have hpredTail : T (j - 1) = h := htail (j - 1) (by omega) (by omega)
          have hjTail : T j = h := htail j (by omega) hjL
          simp [f, g, h2, lowerTailVector, hjnot, hprednot, hpredTail, hjTail]
      · simp [f, g, h2]
    · intro hnot
      exact absurd (by simp [hSL]) hnot
  have hSdiff :
      g S - f S = (h - J) * (n (S + 1) - J) := by
    have hpredlt : S - 1 < S := by omega
    have hSTail : T S = h := htail S le_rfl hSL
    simp [f, g, hS, lowerTailVector, hpredlt, hpred, hSTail]
  have hdiff' :
      (∑ j ∈ Finset.range (L + 1), (g j - f j)) =
        (h - J) * (n (S + 1) - J) := by
    simpa [hSdiff] using hdiff
  have hsum :
      (∑ j ∈ Finset.range (L + 1), g j) =
        (∑ j ∈ Finset.range (L + 1), f j) + (h - J) * (n (S + 1) - J) := by
    calc
      (∑ j ∈ Finset.range (L + 1), g j)
          = ∑ j ∈ Finset.range (L + 1), (f j + (g j - f j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = (∑ j ∈ Finset.range (L + 1), f j) +
            ∑ j ∈ Finset.range (L + 1), (g j - f j) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ j ∈ Finset.range (L + 1), f j) +
            (h - J) * (n (S + 1) - J) := by
              rw [hdiff']
  unfold terminalExponent
  rw [hbase, hsum]
  ring

/-- Packaged flat-tail form of the Case 1 terminal-exponent increment. -/
theorem FlatTailFromPred.terminalExponent_lowerTailVector
    {L S : ℕ} {n T : ℕ → ℤ} {h J : ℤ}
    (hflat : FlatTailFromPred L S T h)
    (hS : 2 ≤ S) (hSL : S ≤ L) :
    terminalExponent L n (lowerTailVector T S J) =
      terminalExponent L n T + (h - J) * (n (S + 1) - J) :=
  terminalExponent_lowerTailVector_of_flatFromPred L S n T h J hS hSL
    hflat.pred hflat.tail

/-- Case 1 algebraic form: a flat level `J + J1` gives the displayed increment term. -/
theorem terminalExponent_lowerTailVector_of_flatFromPred_add
    (L S : ℕ) (n T : ℕ → ℤ) (J J1 : ℤ)
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (hpred : T (S - 1) = J + J1)
    (htail : ∀ i, S ≤ i → i ≤ L → T i = J + J1) :
    terminalExponent L n (lowerTailVector T S J) =
      terminalExponent L n T + J1 * (n (S + 1) - J) := by
  rw [terminalExponent_lowerTailVector_of_flatFromPred L S n T (J + J1) J
    hS hSL hpred htail]
  ring

/-- Packaged algebraic form: a flat level `J+J1` gives the source increment term. -/
theorem FlatTailFromPred.terminalExponent_lowerTailVector_add
    {L S : ℕ} {n T : ℕ → ℤ} {J J1 : ℤ}
    (hflat : FlatTailFromPred L S T (J + J1))
    (hS : 2 ≤ S) (hSL : S ≤ L) :
    terminalExponent L n (lowerTailVector T S J) =
      terminalExponent L n T + J1 * (n (S + 1) - J) :=
  terminalExponent_lowerTailVector_of_flatFromPred_add L S n T J J1 hS hSL
    hflat.pred hflat.tail

/-- Conditional one-label certificate transformer for tail lowering. -/
theorem LabelExponentCertificate.lowerTailVector_of_flatFromPred_add
    {L S Jstate s k : ℕ} {n : ℕ → ℕ} {T : ℕ → ℤ} {numerator J J1 : ℤ}
    (hcert : LabelExponentCertificate L n S Jstate s k T numerator (J + J1))
    (hflat : FlatTailFromPred L S T (J + J1))
    (hS : 2 ≤ S) (hSL : S ≤ L) (hJle : J ≤ J + J1) :
    LabelExponentCertificate L n S Jstate s k (lowerTailVector T S J)
      (numerator + J1 * ((n (S + 1) : ℤ) - J)) J where
  introduced := hcert.introduced
  terminalExponent_eq := by
    rw [hflat.terminalExponent_lowerTailVector_add (n := widthZ n) hS hSL,
      hcert.terminalExponent_eq]
    simp [widthZ]
  least_value := by
    constructor
    · exact ⟨S, by simp [Finset.mem_Icc, (by omega : 1 ≤ S), hSL], lowerTailVector_self T S J⟩
    · intro v hv
      rcases hv with ⟨i, hi, hvi⟩
      rw [← hvi]
      by_cases hiS : i < S
      · rw [lowerTailVector_eq_of_lt hiS]
        exact le_trans hJle (hcert.least_value.2 ⟨i, hi, rfl⟩)
      · rw [lowerTailVector_eq_of_le (le_of_not_gt hiS)]

/-- Case 1 selected-label certificate update from source level data, assuming the
level is already the old certificate least value and the flat-tail invariant is supplied. -/
theorem Case1FirstJumpHypotheses.lowerTailVector_labelExponentCertificate
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ} {numerator : ℤ}
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s k level vector)
    (hcert :
      LabelExponentCertificate L n S J s k (vector s k) numerator (level s k : ℤ))
    (hflat : FlatTailFromPred L S (vector s k) (level s k : ℤ))
    (hS : 2 ≤ S) (hSL : S ≤ L) :
    LabelExponentCertificate L n S J s k
      (lowerTailVector (vector s k) S (J : ℤ))
      (numerator + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) (J : ℤ) := by
  have hlevel : (level s k : ℤ) = (J : ℤ) + (J1 : ℤ) := by
    simpa using hfirst.selectedLevel_int
  rw [hlevel] at hcert hflat
  exact hcert.lowerTailVector_of_flatFromPred_add hflat hS hSL (by omega)

/-- Conditional Case 1 same-domain certificate update for the selected old label.
All non-selected introduced labels are assumed unchanged. -/
theorem IntroducedLabelExponentCertificates.case1_selectedLowerTail_sameDomain
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hlevelLeast : leastValue s0 k0 = (level s0 k0 : ℤ))
    (hflat : FlatTailFromPred L S (t s0 k0) (level s0 k0 : ℤ))
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (ht_selected : t' s0 k0 = lowerTailVector (t s0 k0) S (J : ℤ))
    (hn_selected :
      numerator' s0 k0 =
        numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ)))
    (hl_selected : leastValue' s0 k0 = (J : ℤ))
    (ht_old :
      ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
        t' s k = t s k)
    (hn_old :
      ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
        numerator' s k = numerator s k)
    (hl_old :
      ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
        leastValue' s k = leastValue s k) :
    IntroducedLabelExponentCertificates L n S J t' numerator' leastValue' := by
  refine hcert.updateSelected ?_ ht_old hn_old hl_old
  have hselectedCert :
      LabelExponentCertificate L n S J s0 k0 (t s0 k0) (numerator s0 k0)
        (level s0 k0 : ℤ) := by
    simpa [hlevelLeast] using hcert.certificate hfirst.selectedIntroduced
  have hnew :=
    hfirst.lowerTailVector_labelExponentCertificate hselectedCert hflat hS hSL
  rw [ht_selected, hn_selected, hl_selected]
  exact hnew

/-- Convenience form of the conditional Case 1 same-domain update using explicit
selected-label data overrides. This is still only certificate bookkeeping. -/
theorem IntroducedLabelExponentCertificates.case1_selectedLowerTail_updateData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hlevelLeast : leastValue s0 k0 = (level s0 k0 : ℤ))
    (hflat : FlatTailFromPred L S (t s0 k0) (level s0 k0 : ℤ))
    (hS : 2 ≤ S) (hSL : S ≤ L) :
    IntroducedLabelExponentCertificates L n S J
      (updateSelectedLabelVector s0 k0 (lowerTailVector (t s0 k0) S (J : ℤ)) t)
      (updateSelectedLabelScalar s0 k0
        (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar s0 k0 (J : ℤ) leastValue) := by
  refine hcert.case1_selectedLowerTail_sameDomain hfirst hlevelLeast hflat hS hSL
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact funext fun i ↦ updateSelectedLabelVector_selected s0 k0
      (lowerTailVector (t s0 k0) S (J : ℤ)) t i
  · exact updateSelectedLabelScalar_selected s0 k0
      (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator
  · exact updateSelectedLabelScalar_selected s0 k0 (J : ℤ) leastValue
  · intro s k _ hne
    exact funext fun i ↦ updateSelectedLabelVector_of_ne
      (lowerTailVector (t s0 k0) S (J : ℤ)) t i hne
  · intro s k _ hne
    exact updateSelectedLabelScalar_of_ne
      (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator hne
  · intro s k _ hne
    exact updateSelectedLabelScalar_of_ne (J : ℤ) leastValue hne

/-- Conditional level and above-pivot flat-tail bridges for labels introduced at a state. -/
structure IntroducedLabelLevelTailInvariants
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (level : ℕ → ℕ → ℕ)
    (t : ℕ → ℕ → ℕ → ℤ) (leastValue : ℕ → ℕ → ℤ) : Prop where
  leastValue_eq_level :
    ∀ {s k}, introducedLabel L n S J s k → leastValue s k = (level s k : ℤ)
  flatTail_abovePivot :
    ∀ {s k}, introducedLabel L n S J s k → J < level s k →
      FlatTailFromPred L S (t s k) (level s k : ℤ)

/-- If the level/above-pivot flat-tail bridge is supplied, the Case 1 same-domain
update-data theorem no longer needs separate selected-label bridge hypotheses. -/
theorem IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_levelTailInvariants
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hinv : IntroducedLabelLevelTailInvariants L n S J level t leastValue)
    (hS : 2 ≤ S) (hSL : S ≤ L) :
    IntroducedLabelExponentCertificates L n S J
      (updateSelectedLabelVector s0 k0 (lowerTailVector (t s0 k0) S (J : ℤ)) t)
      (updateSelectedLabelScalar s0 k0
        (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar s0 k0 (J : ℤ) leastValue) :=
  hcert.case1_selectedLowerTail_updateData hfirst
    (hinv.leastValue_eq_level hfirst.selectedIntroduced)
    (hinv.flatTail_abovePivot hfirst.selectedIntroduced hfirst.lt_selectedLevel) hS hSL

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

/-- Divisibility data supplies the right-oriented quotient witnesses used by `P`. -/
theorem exists_right_quotients_of_forall_dvd
    {ι : Type*} {b0 : α} {b : ι → α} (h : ∀ i, b0 ∣ b i) :
    ∃ q : ι → α, ∀ i, b i = q i * b0 := by
  choose q hq using h
  refine ⟨q, ?_⟩
  intro i
  rw [hq i]
  ac_rfl

/-- Equal row weights admit the trivial right-oriented quotient witnesses. -/
theorem exists_right_quotients_of_forall_eq
    {ι : Type*} {b0 : α} {b : ι → α} (h : ∀ i, b i = b0) :
    ∃ q : ι → α, ∀ i, b i = q i * b0 :=
  ⟨fun _ ↦ 1, by intro i; rw [h i]; simp⟩

/-- Equality with the pivot weight, or divisibility by it, supplies quotient witnesses. -/
theorem exists_right_quotients_of_forall_eq_or_dvd
    {ι : Type*} {b0 : α} {b : ι → α} (h : ∀ i, b i = b0 ∨ b0 ∣ b i) :
    ∃ q : ι → α, ∀ i, b i = q i * b0 :=
  exists_right_quotients_of_forall_dvd (fun i ↦ by
    rcases h i with hi | hdiv
    · simp [hi]
    · exact hdiv)

/-- Tail-product form with the quotient explicitly on the right. -/
theorem monomialRec_tail_eq_right_mul (step : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    monomialRec step b = monomialTail step a (b - a) * monomialRec step a := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  subst hk
  rw [Nat.add_sub_cancel_left, monomialRec_add_eq_tail_mul]

/-- Monomial recurrence terms later than `a` admit right quotient witnesses over `b_a`. -/
theorem exists_right_quotients_monomialRec_of_le
    (step : ℕ → α) {ι : Type*} {a : ℕ} {level : ι → ℕ}
    (hlevel : ∀ i, a ≤ level i) :
    ∃ q : ι → α, ∀ i, monomialRec step (level i) = q i * monomialRec step a :=
  exists_right_quotients_of_forall_dvd (fun i ↦ monomialRec_dvd_of_le step (hlevel i))

/-- Equal pivot-strip weights or later recurrence levels admit quotient witnesses over `b_a`. -/
theorem exists_right_quotients_monomialRec_of_eq_or_le
    (step : ℕ → α) {ι : Type*} {a : ℕ} {level : ι → ℕ}
    (hlevel : ∀ i, monomialRec step (level i) = monomialRec step a ∨ a ≤ level i) :
    ∃ q : ι → α, ∀ i, monomialRec step (level i) = q i * monomialRec step a :=
  exists_right_quotients_of_forall_eq_or_dvd (fun i ↦
    (hlevel i).imp id (fun hle ↦ monomialRec_dvd_of_le step hle))

/-- Common pivot multiplication preserves right quotient witnesses for monomial recurrence terms. -/
theorem exists_right_quotients_pivotMul_monomialRec_of_le
    (step : ℕ → α) (u : α) {ι : Type*} {a : ℕ} {level : ι → ℕ}
    (hlevel : ∀ i, a ≤ level i) :
    ∃ q : ι → α, ∀ i,
      u * monomialRec step (level i) = q i * (u * monomialRec step a) :=
  exists_right_quotients_of_forall_dvd
    (fun i ↦ pivotMul_monomialRec_dvd_of_le step u (hlevel i))

/-- Common pivot multiplication preserves equality-or-later recurrence quotient witnesses. -/
theorem exists_right_quotients_pivotMul_monomialRec_of_eq_or_le
    (step : ℕ → α) (u : α) {ι : Type*} {a : ℕ} {level : ι → ℕ}
    (hlevel : ∀ i, monomialRec step (level i) = monomialRec step a ∨ a ≤ level i) :
    ∃ q : ι → α, ∀ i,
      u * monomialRec step (level i) = q i * (u * monomialRec step a) :=
  exists_right_quotients_of_forall_eq_or_dvd (fun i ↦ by
    rcases hlevel i with heq | hle
    · left
      rw [heq]
    · right
      exact pivotMul_monomialRec_dvd_of_le step u hle)

/-- Constant row weights admit the trivial quotient witnesses. -/
theorem exists_right_quotients_const {ι : Type*} (b0 : α) :
    ∃ q : ι → α, ∀ i, b0 = q i * b0 :=
  ⟨fun _ ↦ 1, by intro i; simp⟩

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

/-- Divisibility of every lower-row weight by the pivot weight supplies a `P` matrix. -/
theorem exists_weightedPivotBlockRowOp_mul_diagonal_mul_of_forall_dvd
    (b0 : R) (b x : ρ → R) (D : Matrix ρ κ R)
    (hdiv : ∀ i, b0 ∣ b i) :
    ∃ q : ρ → R,
      weightedPivotBlockRowOp q x * weightedPivotDiagonal b0 b * weightedPivotBlockMatrix x D =
        weightedPivotDiagonal b0 b * weightedPivotClearedBlock D := by
  rcases exists_right_quotients_of_forall_dvd hdiv with ⟨q, hq⟩
  exact ⟨q, weightedPivotBlockRowOp_mul_diagonal_mul b0 b q x D hq⟩

end RowOperationBlocks

section ColumnOperationBlocks

variable {R ρ κ τ : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]

/-- The pre-`Q` pivot block, with top row `[1 y]`. -/
def pivotPreQBlock (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R) :
    Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R :=
  fromBlocks 1 y x D

/-- Indices other than a chosen pivot. -/
abbrev pivotComplement {ι : Type*} (pivot : ι) := {i : ι // i ≠ pivot}

/-- The reindexing equivalence that puts a selected pivot first. -/
noncomputable def pivotFirstIndexEquiv {ι : Type*} [DecidableEq ι] (pivot : ι) :
    Unit ⊕ pivotComplement pivot ≃ ι where
  toFun
    | Sum.inl _ => pivot
    | Sum.inr i => i.1
  invFun i := if h : i = pivot then Sum.inl () else Sum.inr ⟨i, h⟩
  left_inv := by
    intro i
    rcases i with (_ | i)
    · simp
    · simp [i.2]
  right_inv := by
    intro i
    by_cases h : i = pivot
    · simp [h]
    · simp [h]

/-- Reindex a matrix so a chosen pivot row and column are first. -/
def pivotFirstMatrix {ι κ R : Type*} [DecidableEq ι] [DecidableEq κ]
    (rowPivot : ι) (colPivot : κ) (A : Matrix ι κ R) :
    Matrix (Unit ⊕ pivotComplement rowPivot) (Unit ⊕ pivotComplement colPivot) R :=
  A.submatrix (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)

/-- The lower-left column of a pivot-first block. -/
def pivotFirstX {ι κ R : Type*} (rowPivot : ι) (colPivot : κ) (A : Matrix ι κ R) :
    Matrix (pivotComplement rowPivot) Unit R :=
  fun i _ ↦ A i.1 colPivot

/-- The upper-right row of a pivot-first block. -/
def pivotFirstY {ι κ R : Type*} (rowPivot : ι) (colPivot : κ) (A : Matrix ι κ R) :
    Matrix Unit (pivotComplement colPivot) R :=
  fun _ j ↦ A rowPivot j.1

/-- The lower-right block of a pivot-first block. -/
def pivotFirstD {ι κ R : Type*} (rowPivot : ι) (colPivot : κ) (A : Matrix ι κ R) :
    Matrix (pivotComplement rowPivot) (pivotComplement colPivot) R :=
  fun i j ↦ A i.1 j.1

/-- Reindex a following factor so its rows match the pivot-first column order. -/
def pivotFirstFollowingFactor {κ τ R : Type*} [DecidableEq κ]
    (colPivot : κ) (C : Matrix κ τ R) :
    Matrix (Unit ⊕ pivotComplement colPivot) τ R :=
  C.submatrix (pivotFirstIndexEquiv colPivot) id

@[simp] theorem pivotFirstMatrix_inl_inl {ι κ R : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (rowPivot : ι) (colPivot : κ) (A : Matrix ι κ R) :
    pivotFirstMatrix rowPivot colPivot A (Sum.inl ()) (Sum.inl ()) =
      A rowPivot colPivot :=
  rfl

@[simp] theorem pivotFirstMatrix_inl_inr {ι κ R : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (rowPivot : ι) (colPivot : κ) (A : Matrix ι κ R)
    (j : pivotComplement colPivot) :
    pivotFirstMatrix rowPivot colPivot A (Sum.inl ()) (Sum.inr j) =
      A rowPivot j.1 :=
  rfl

@[simp] theorem pivotFirstMatrix_inr_inl {ι κ R : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (rowPivot : ι) (colPivot : κ) (A : Matrix ι κ R)
    (i : pivotComplement rowPivot) :
    pivotFirstMatrix rowPivot colPivot A (Sum.inr i) (Sum.inl ()) =
      A i.1 colPivot :=
  rfl

@[simp] theorem pivotFirstMatrix_inr_inr {ι κ R : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (rowPivot : ι) (colPivot : κ) (A : Matrix ι κ R)
    (i : pivotComplement rowPivot) (j : pivotComplement colPivot) :
    pivotFirstMatrix rowPivot colPivot A (Sum.inr i) (Sum.inr j) =
      A i.1 j.1 :=
  rfl

/-- A pivot-first reindexed matrix with pivot entry `1` has the normalised pivot-block shape. -/
theorem pivotFirstMatrix_eq_pivotPreQBlock
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1) :
    pivotFirstMatrix rowPivot colPivot A =
      pivotPreQBlock
        (pivotFirstX rowPivot colPivot A)
        (pivotFirstY rowPivot colPivot A)
        (pivotFirstD rowPivot colPivot A) := by
  ext i j
  rcases i with (_ | i)
  · rcases j with (_ | j)
    · exact hA
    · rfl
  · rcases j with (_ | j)
    · rfl
    · rfl

/-- Multiplying by a pivot-first following factor is just the pre-reindexed product
reindexed in the pivot-first row order. -/
theorem pivotFirstMatrix_mul_pivotFirstFollowingFactor
    {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    {rowPivot : ι} {colPivot : κ} [Fintype (pivotComplement colPivot)]
    (A : Matrix ι κ R) (C : Matrix κ τ R) :
    pivotFirstMatrix rowPivot colPivot A * pivotFirstFollowingFactor colPivot C =
      (A * C).submatrix (pivotFirstIndexEquiv rowPivot) id := by
  rw [pivotFirstMatrix, pivotFirstFollowingFactor, submatrix_mul_equiv]

/-- The split pivot-row diagonal is the original diagonal weight matrix in pivot-first
row coordinates. -/
theorem weightedPivotDiagonal_eq_pivotFirst_diagonal
    {ι : Type*} [DecidableEq ι] (rowPivot : ι) (weight : ι → R) :
    weightedPivotDiagonal (weight rowPivot)
        (fun i : pivotComplement rowPivot ↦ weight i.1) =
      (diagonal weight).submatrix
        (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv rowPivot) := by
  ext i j
  rcases i with (_ | i)
  · rcases j with (_ | j)
    · simp [weightedPivotDiagonal, pivotFirstIndexEquiv]
    · have hne : rowPivot ≠ j.1 := fun h ↦ j.2 h.symm
      simp [weightedPivotDiagonal, pivotFirstIndexEquiv, diagonal_apply_ne weight hne]
  · rcases j with (_ | j)
    · simp [weightedPivotDiagonal, pivotFirstIndexEquiv, diagonal_apply_ne weight i.2]
    · by_cases hij : i = j
      · subst hij
        simp [weightedPivotDiagonal, pivotFirstIndexEquiv]
      · have hij_val : i.1 ≠ j.1 := by
          intro h
          exact hij (Subtype.ext h)
        simp [weightedPivotDiagonal, pivotFirstIndexEquiv, hij, hij_val]

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

/-- Pure algebra: the normalised `Q/P` identity after pivot-first reindexing.
This assumes pivot entry `1`, quotient witnesses, and pivot-first coordinates;
it proves no chart construction, coverage, transition invariant, exponent
update, or Jacobian fact. -/
theorem weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)] [DecidableEq (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)] [DecidableEq (pivotComplement colPivot)]
    (b0 : R) (b q : pivotComplement rowPivot → R)
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1)
    (h : ∀ i, b i = q i * b0) :
    weightedPivotBlockRowOp q (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
        weightedPivotDiagonal b0 b *
        (pivotFirstMatrix rowPivot colPivot A *
          pivotQ (pivotFirstY rowPivot colPivot A)) =
      weightedPivotDiagonal b0 b *
        weightedPivotClearedBlock
          (pivotFirstD rowPivot colPivot A -
            pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A) := by
  rw [pivotFirstMatrix_eq_pivotPreQBlock A hA]
  exact
    weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ
      b0 b q
      (pivotFirstX rowPivot colPivot A)
      (pivotFirstY rowPivot colPivot A)
      (pivotFirstD rowPivot colPivot A)
      h

/-- Pivot-first `Q/P` identity with the quotient witnesses chosen from divisibility.
This is still pure algebra in already-normalised pivot-first coordinates. -/
theorem exists_pivotFirstQP_mul_pivotQ_of_forall_dvd
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)] [DecidableEq (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)] [DecidableEq (pivotComplement colPivot)]
    (b0 : R) (b : pivotComplement rowPivot → R)
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1)
    (hdiv : ∀ i, b0 ∣ b i) :
    ∃ q : pivotComplement rowPivot → R,
      weightedPivotBlockRowOp q (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
          weightedPivotDiagonal b0 b *
          (pivotFirstMatrix rowPivot colPivot A *
            pivotQ (pivotFirstY rowPivot colPivot A)) =
        weightedPivotDiagonal b0 b *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot A -
              pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A) := by
  rcases exists_right_quotients_of_forall_dvd hdiv with ⟨q, hq⟩
  exact ⟨q, weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ
    b0 b q A hA hq⟩

/-- Pivot-first `Q/P` identity for equality-or-later monomial recurrence row weights. -/
theorem exists_pivotFirstQP_mul_pivotQ_of_monomialRec_eq_or_le
    (step : ℕ → R)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)] [DecidableEq (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)] [DecidableEq (pivotComplement colPivot)]
    {a : ℕ} (level : pivotComplement rowPivot → ℕ)
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1)
    (hlevel : ∀ i,
      monomialRec step (level i) = monomialRec step a ∨ a ≤ level i) :
    ∃ q : pivotComplement rowPivot → R,
      weightedPivotBlockRowOp q (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
          weightedPivotDiagonal (monomialRec step a)
            (fun i ↦ monomialRec step (level i)) *
          (pivotFirstMatrix rowPivot colPivot A *
            pivotQ (pivotFirstY rowPivot colPivot A)) =
        weightedPivotDiagonal (monomialRec step a)
            (fun i ↦ monomialRec step (level i)) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot A -
              pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A) := by
  rcases exists_right_quotients_monomialRec_of_eq_or_le step hlevel with ⟨q, hq⟩
  exact ⟨q, weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ
    (monomialRec step a) (fun i ↦ monomialRec step (level i)) q A hA hq⟩

/-- Pivot-first `Q/P` identity for equality-or-later recurrence weights after common
multiplication by the selected pivot variable. -/
theorem exists_pivotFirstQP_mul_pivotQ_of_pivotMul_monomialRec_eq_or_le
    (step : ℕ → R) (u : R)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)] [DecidableEq (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)] [DecidableEq (pivotComplement colPivot)]
    {a : ℕ} (level : pivotComplement rowPivot → ℕ)
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1)
    (hlevel : ∀ i,
      monomialRec step (level i) = monomialRec step a ∨ a ≤ level i) :
    ∃ q : pivotComplement rowPivot → R,
      weightedPivotBlockRowOp q (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
          weightedPivotDiagonal (u * monomialRec step a)
            (fun i ↦ u * monomialRec step (level i)) *
          (pivotFirstMatrix rowPivot colPivot A *
            pivotQ (pivotFirstY rowPivot colPivot A)) =
        weightedPivotDiagonal (u * monomialRec step a)
            (fun i ↦ u * monomialRec step (level i)) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot A -
              pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A) := by
  rcases exists_right_quotients_pivotMul_monomialRec_of_eq_or_le step u hlevel with ⟨q, hq⟩
  exact ⟨q, weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ
    (u * monomialRec step a) (fun i ↦ u * monomialRec step (level i)) q A hA hq⟩

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

/-- Pure algebraic product-preservation form of the pivot-first reindexed `Q/P` identity.
The following factor and weights are already in pivot-first coordinates; this
does not prove chart construction, coverage, transition invariants, exponent
updates, or Jacobian facts. -/
theorem weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul
    {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)] [DecidableEq (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)] [DecidableEq (pivotComplement colPivot)]
    (b0 : R) (b q : pivotComplement rowPivot → R)
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1)
    (C : Matrix (Unit ⊕ pivotComplement colPivot) τ R)
    (h : ∀ i, b i = q i * b0) :
    (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
        weightedPivotDiagonal b0 b * pivotFirstMatrix rowPivot colPivot A) * C =
      (weightedPivotDiagonal b0 b *
        weightedPivotClearedBlock
          (pivotFirstD rowPivot colPivot A -
            pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A)) *
        (pivotQinv (pivotFirstY rowPivot colPivot A) * C) := by
  rw [pivotFirstMatrix_eq_pivotPreQBlock A hA]
  exact
    weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul
      b0 b q
      (pivotFirstX rowPivot colPivot A)
      (pivotFirstY rowPivot colPivot A)
      (pivotFirstD rowPivot colPivot A)
      C h

/-- Pivot-first product-preservation identity with quotient witnesses chosen from divisibility.
This assumes the following factor and weights are already in pivot-first coordinates. -/
theorem exists_pivotFirstQP_mul_of_forall_dvd
    {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)] [DecidableEq (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)] [DecidableEq (pivotComplement colPivot)]
    (b0 : R) (b : pivotComplement rowPivot → R)
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1)
    (C : Matrix (Unit ⊕ pivotComplement colPivot) τ R)
    (hdiv : ∀ i, b0 ∣ b i) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
          weightedPivotDiagonal b0 b * pivotFirstMatrix rowPivot colPivot A) * C =
        (weightedPivotDiagonal b0 b *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot A -
              pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A)) *
          (pivotQinv (pivotFirstY rowPivot colPivot A) * C) := by
  rcases exists_right_quotients_of_forall_dvd hdiv with ⟨q, hq⟩
  exact ⟨q, weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul
    b0 b q A hA C hq⟩

/-- Pivot-first product-preservation identity for equality-or-later recurrence row weights. -/
theorem exists_pivotFirstQP_mul_of_monomialRec_eq_or_le
    (step : ℕ → R)
    {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)] [DecidableEq (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)] [DecidableEq (pivotComplement colPivot)]
    {a : ℕ} (level : pivotComplement rowPivot → ℕ)
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1)
    (C : Matrix (Unit ⊕ pivotComplement colPivot) τ R)
    (hlevel : ∀ i,
      monomialRec step (level i) = monomialRec step a ∨ a ≤ level i) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
          weightedPivotDiagonal (monomialRec step a)
            (fun i ↦ monomialRec step (level i)) *
          pivotFirstMatrix rowPivot colPivot A) * C =
        (weightedPivotDiagonal (monomialRec step a)
            (fun i ↦ monomialRec step (level i)) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot A -
              pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A)) *
          (pivotQinv (pivotFirstY rowPivot colPivot A) * C) := by
  rcases exists_right_quotients_monomialRec_of_eq_or_le step hlevel with ⟨q, hq⟩
  exact ⟨q, weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul
    (monomialRec step a) (fun i ↦ monomialRec step (level i)) q A hA C hq⟩

/-- Pivot-first product-preservation identity for equality-or-later recurrence row weights
after common multiplication by the selected pivot variable. -/
theorem exists_pivotFirstQP_mul_of_pivotMul_monomialRec_eq_or_le
    (step : ℕ → R) (u : R)
    {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)] [DecidableEq (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)] [DecidableEq (pivotComplement colPivot)]
    {a : ℕ} (level : pivotComplement rowPivot → ℕ)
    (A : Matrix ι κ R) (hA : A rowPivot colPivot = 1)
    (C : Matrix (Unit ⊕ pivotComplement colPivot) τ R)
    (hlevel : ∀ i,
      monomialRec step (level i) = monomialRec step a ∨ a ≤ level i) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
          weightedPivotDiagonal (u * monomialRec step a)
            (fun i ↦ u * monomialRec step (level i)) *
          pivotFirstMatrix rowPivot colPivot A) * C =
        (weightedPivotDiagonal (u * monomialRec step a)
            (fun i ↦ u * monomialRec step (level i)) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot A -
              pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A)) *
          (pivotQinv (pivotFirstY rowPivot colPivot A) * C) := by
  rcases exists_right_quotients_pivotMul_monomialRec_of_eq_or_le step u hlevel with ⟨q, hq⟩
  exact ⟨q, weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul
    (u * monomialRec step a) (fun i ↦ u * monomialRec step (level i)) q A hA C hq⟩

/-- Source-displayed Case 2 top-left selected-entry substitution instantiates the
pivot-first product `Q/P` identity under flat residual-row weights.  The selected
variable has already been factored into the row weights as `u * weight`; this is
not an arbitrary-pivot chart or chart-coverage theorem. -/
theorem exists_case2DisplayedQP_mul_of_flat_weights
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (hflat : ∀ i, weight i = weight (case2DisplayedPivotRow n hS hcont)) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (selectedEntryNormalizedMatrix
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont) residual) i ()) *
          weightedPivotDiagonal
            (u * weight (case2DisplayedPivotRow n hS hcont))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * weight i.1) *
          pivotFirstMatrix
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (selectedEntryNormalizedMatrix
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont) residual)) *
          C =
        (weightedPivotDiagonal
            (u * weight (case2DisplayedPivotRow n hS hcont))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * weight i.1) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont)
                (selectedEntryNormalizedMatrix
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont) residual) -
              pivotFirstX
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont)
                  (selectedEntryNormalizedMatrix
                    (case2DisplayedPivotRow n hS hcont)
                    (case2DisplayedPivotCol n hS hcont) residual) *
                pivotFirstY
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont)
                  (selectedEntryNormalizedMatrix
                    (case2DisplayedPivotRow n hS hcont)
                    (case2DisplayedPivotCol n hS hcont) residual))) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (selectedEntryNormalizedMatrix
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont) residual)) * C) := by
  refine exists_pivotFirstQP_mul_of_forall_dvd
    (u * weight (case2DisplayedPivotRow n hS hcont))
    (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦ u * weight i.1)
    (selectedEntryNormalizedMatrix
      (case2DisplayedPivotRow n hS hcont)
      (case2DisplayedPivotCol n hS hcont) residual)
    (selectedEntryNormalizedMatrix_pivot
      (case2DisplayedPivotRow n hS hcont)
      (case2DisplayedPivotCol n hS hcont) residual)
    C ?_
  intro i
  change
    u * weight (case2DisplayedPivotRow n hS hcont) ∣
      u * weight i.1
  rw [hflat i.1]

/-- The normalised residual block for the source-displayed Case 2 pivot. -/
def case2DisplayedNormalizedMatrix
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  selectedEntryNormalizedMatrix
    (case2DisplayedPivotRow n hS hcont)
    (case2DisplayedPivotCol n hS hcont) residual

/-- The following factor for displayed Case 2, reindexed into pivot-first column order. -/
def case2DisplayedFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  pivotFirstFollowingFactor (case2DisplayedPivotCol n hS hcont) C

/-- Displayed Case 2 following-factor transport for the normalised residual block. -/
theorem case2DisplayedNormalizedMatrix_mul_followingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    pivotFirstMatrix
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case2DisplayedNormalizedMatrix n hS hcont residual) *
      case2DisplayedFollowingFactor n hS hcont C =
    (case2DisplayedNormalizedMatrix n hS hcont residual * C).submatrix
      (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont)) id := by
  exact pivotFirstMatrix_mul_pivotFirstFollowingFactor
    (case2DisplayedNormalizedMatrix n hS hcont residual) C

/-- Source-displayed Case 2 top-left `Q/P` identity with the following factor reindexed
into pivot-first column coordinates. This is still local finite algebra, not chart coverage. -/
theorem exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R)
    (hflat : ∀ i, weight i = weight (case2DisplayedPivotRow n hS hcont)) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          weightedPivotDiagonal
            (u * weight (case2DisplayedPivotRow n hS hcont))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * weight i.1) *
          pivotFirstMatrix
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (case2DisplayedNormalizedMatrix n hS hcont residual)) *
          case2DisplayedFollowingFactor n hS hcont C =
        (weightedPivotDiagonal
            (u * weight (case2DisplayedPivotRow n hS hcont))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * weight i.1) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont)
                (case2DisplayedNormalizedMatrix n hS hcont residual) -
              pivotFirstX
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont)
                  (case2DisplayedNormalizedMatrix n hS hcont residual) *
                pivotFirstY
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont)
                  (case2DisplayedNormalizedMatrix n hS hcont residual))) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual)) *
            case2DisplayedFollowingFactor n hS hcont C) := by
  simpa [case2DisplayedNormalizedMatrix, case2DisplayedFollowingFactor] using
    exists_case2DisplayedQP_mul_of_flat_weights
      n hS hcont u weight residual
      (case2DisplayedFollowingFactor n hS hcont C) hflat

end ColumnOperationBlocks

end Aoyagi
end DLN
end DLNFibre
