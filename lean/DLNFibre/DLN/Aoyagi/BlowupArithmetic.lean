import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic
import DLNFibre.DLN.Aoyagi.EntryIdeal
import DLNFibre.DLN.Aoyagi.MatrixChain

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

/-- Finite actual-width source labels, represented as dependent pairs `(s,k)`. -/
def actualWidthLabelFinset (L : ℕ) (n : ℕ → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 L).sigma fun s ↦ Finset.Icc 1 (n (s + 1))

/-- Membership in the finite actual-width label set is exactly `actualWidthLabel`. -/
theorem mem_actualWidthLabelFinset {L : ℕ} {n : ℕ → ℕ} {p : Σ _ : ℕ, ℕ} :
    p ∈ actualWidthLabelFinset L n ↔ actualWidthLabel L n p.1 p.2 := by
  simp only [actualWidthLabelFinset, actualWidthLabel, Finset.mem_sigma, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hs1, hsL⟩, hk1, hkN⟩
    exact ⟨hs1, hsL, hk1, hkN⟩
  · rintro ⟨hs1, hsL, hk1, hkN⟩
    exact ⟨⟨hs1, hsL⟩, hk1, hkN⟩

/-- Finite introduced labels at state `(S,J)`. -/
def introducedLabelFinset (L : ℕ) (n : ℕ → ℕ) (S J : ℕ) :
    Finset (Σ _ : ℕ, ℕ) :=
  (actualWidthLabelFinset L n).filter fun p ↦ p.1 < S ∨ p.1 = S ∧ p.2 ≤ J

/-- Membership in the finite introduced-label set is exactly `introducedLabel`. -/
theorem mem_introducedLabelFinset
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : Σ _ : ℕ, ℕ} :
    p ∈ introducedLabelFinset L n S J ↔ introducedLabel L n S J p.1 p.2 := by
  simp [introducedLabelFinset, introducedLabel, mem_actualWidthLabelFinset]

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

/-- The printed Case 2 vector differs from the prefix-minimum formula by the
row-width discrepancy times the remaining column factor. -/
theorem terminalExponent_printedCase2Vector_sub_prefixFormula
    (L S : ℕ) (n : ℕ → ℤ) (J : ℤ) (hS : 1 ≤ S) (hSL : S ≤ L) :
    terminalExponent L n (printedCase2Vector n S J) -
      (prefixMin n S - J) * (n (S + 1) - J) =
      (n S - prefixMin n S) * (n (S + 1) - J) := by
  rw [terminalExponent_printedCase2Vector L S n J hS hSL]
  ring

/-- The printed Case 2 vector has the prefix-minimum exponent exactly in the
equal-row-width or zero-column-factor cases. -/
theorem terminalExponent_printedCase2Vector_eq_prefixFormula_iff
    (L S : ℕ) (n : ℕ → ℕ) (J : ℕ) (hS : 1 ≤ S) (hSL : S ≤ L) :
    terminalExponent L (widthZ n) (printedCase2Vector (widthZ n) S (J : ℤ)) =
        ((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ)) ↔
      n S = prefixMinNat n S ∨ n (S + 1) = J := by
  rw [terminalExponent_printedCase2Vector L S (widthZ n) (J : ℤ) hS hSL]
  simp only [widthZ]
  constructor
  · intro h
    by_cases hfactor : ((n (S + 1) : ℤ) - (J : ℤ)) = 0
    · right
      omega
    · left
      have hleft :
          ((n S : ℤ) - (J : ℤ)) =
            ((prefixMinNat n S : ℤ) - (J : ℤ)) :=
        mul_right_cancel₀ hfactor h
      omega
  · intro h
    rcases h with hwidth | hcol
    · rw [hwidth]
    · rw [hcol]
      ring

/-- Under a genuine prefix-width drop and the Case 2 continuation bound, the
printed vector cannot have the corrected terminal exponent. -/
theorem terminalExponent_case2Printed_ne_corrected_of_prefixDrop_of_cont
    (L S : ℕ) (n : ℕ → ℕ) (J : ℕ)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hwidth : prefixMinNat n S < n S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    terminalExponent L (widthZ n) (printedCase2Vector (widthZ n) S (J : ℤ)) ≠
      terminalExponent L (widthZ n) (correctedCase2PivotVector n S J) := by
  rw [terminalExponent_printedCase2Vector L S (widthZ n) (J : ℤ) hS hSL,
    terminalExponent_correctedCase2PivotVector L S n J hS hSL]
  simp only [widthZ]
  intro h
  have hfactor : ((n (S + 1) : ℤ) - (J : ℤ)) ≠ 0 := by
    have hcol : J < n (S + 1) := by
      exact lt_of_lt_of_le (Nat.lt_succ_self J)
        (le_trans hcont (prefixMinNat_le_width n (by omega : 1 ≤ S + 1)))
    omega
  have hleft :
      ((n S : ℤ) - (J : ℤ)) =
        ((prefixMinNat n S : ℤ) - (J : ℤ)) :=
    mul_right_cancel₀ hfactor h
  omega

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

/-- Advancing `J` adds exactly the next current-layer label to the finite domain,
provided that label is source-valid. -/
theorem introducedLabelFinset_succ_eq_insert
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : actualWidthLabel L n S (J + 1)) :
    introducedLabelFinset L n S (J + 1) =
      insert (Sigma.mk S (J + 1)) (introducedLabelFinset L n S J) := by
  ext p
  constructor
  · intro hp
    have hintro : introducedLabel L n S (J + 1) p.1 p.2 :=
      (mem_introducedLabelFinset.mp hp)
    rcases introducedLabel_succ_cases hintro with hOld | hnew'
    · exact Finset.mem_insert_of_mem (mem_introducedLabelFinset.mpr hOld)
    · rcases hnew' with ⟨hs, hk⟩
      rcases p with ⟨s, k⟩
      simp only [Finset.mem_insert, Sigma.mk.injEq, heq_eq_eq] at hs hk ⊢
      exact Or.inl ⟨hs, hk⟩
  · intro hp
    rcases (Finset.mem_insert.mp hp) with hpnew | hpold
    · subst hpnew
      exact mem_introducedLabelFinset.mpr
        ⟨hnew, Or.inr ⟨rfl, le_rfl⟩⟩
    · exact mem_introducedLabelFinset.mpr
        (introducedLabel_mono_J (by omega : J ≤ J + 1)
          (mem_introducedLabelFinset.mp hpold))

/-- The would-be new current-layer label is not already in the previous
introduced-label finite domain. -/
theorem not_mem_introducedLabelFinset_case2_new_before
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ) :
    Sigma.mk S (J + 1) ∉ introducedLabelFinset L n S J := by
  rw [mem_introducedLabelFinset]
  exact not_introducedLabel_case2_new_before L n S J

/-- A one-step current-layer advance increases the finite introduced-label
domain cardinality by exactly one. -/
theorem introducedLabelFinset_card_succ_eq_succ
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : actualWidthLabel L n S (J + 1)) :
    (introducedLabelFinset L n S (J + 1)).card =
      (introducedLabelFinset L n S J).card + 1 := by
  rw [introducedLabelFinset_succ_eq_insert hnew]
  exact Finset.card_insert_of_notMem
    (not_mem_introducedLabelFinset_case2_new_before L n S J)

/-- If the actual next width is exhausted at `J+1`, then old `(S,J+1)`
introduced labels are exactly the labels at `(S+1,0)`.

This is finite domain bookkeeping only.  Without the actual-width side
condition `n(S+1)=J+1`, the row-exhausted terminal side can add labels in
layer `S` when moving to `(S+1,0)`. -/
theorem introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq
    (L : ℕ) (n : ℕ → ℕ) {S J s k : ℕ}
    (hwidth : n (S + 1) = J + 1) :
    introducedLabel L n S (J + 1) s k ↔
      introducedLabel L n (S + 1) 0 s k := by
  constructor
  · intro h
    rcases h with ⟨hlabel, hs | ⟨hs, _hk⟩⟩
    · exact ⟨hlabel, Or.inl (by omega)⟩
    · exact ⟨hlabel, Or.inl (by omega)⟩
  · intro h
    rcases h with ⟨hlabel, hs | ⟨hs, hk⟩⟩
    · refine ⟨hlabel, ?_⟩
      by_cases hsS : s < S
      · exact Or.inl hsS
      · have hseq : s = S := by omega
        subst hseq
        exact Or.inr ⟨rfl, by simpa [hwidth] using hlabel.2.2.2⟩
    · have hkpos : 1 ≤ k := hlabel.2.2.1
      omega

/-- Finite-set version of
`introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq`. -/
theorem introducedLabelFinset_currentSucc_eq_succStage_zero_of_nextWidth_eq
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hwidth : n (S + 1) = J + 1) :
    introducedLabelFinset L n S (J + 1) =
      introducedLabelFinset L n (S + 1) 0 := by
  ext p
  rw [mem_introducedLabelFinset, mem_introducedLabelFinset]
  exact introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq
    L n hwidth

/-- A current-layer label above the processed index is not introduced at the
current state. -/
theorem not_introducedLabel_current_of_lt_index
    (L : ℕ) (n : ℕ → ℕ) {S J k : ℕ} (hk : J < k) :
    ¬ introducedLabel L n S J S k := by
  intro h
  rcases h.2 with hslt | ⟨_hs, hkJ⟩
  · omega
  · omega

/-- If the actual next width still contains `J+2`, advancing from old
`(S,J+1)` to `(S+1,0)` introduces an extra actual-width label.

This is the row-side obstruction to treating the terminal frontier equality
`M(S+1)=J+1` as an unconditional domain relabel. -/
theorem introducedLabel_succStage_zero_extra_witness_of_nextWidth_ge
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L) (hwidth : J + 2 ≤ n (S + 1)) :
    introducedLabel L n (S + 1) 0 S (J + 2) ∧
      ¬ introducedLabel L n S (J + 1) S (J + 2) := by
  constructor
  · exact introducedLabel_of_lt_stage
      ⟨hS, hSL, by omega, hwidth⟩
      (by omega : S < S + 1)
  · exact not_introducedLabel_current_of_lt_index L n (by omega : J + 1 < J + 2)

/-- Terminal-exponent/minimum certificates for all labels introduced at a state. -/
structure IntroducedLabelExponentCertificates
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (t : ℕ → ℕ → ℕ → ℤ) (numerator leastValue : ℕ → ℕ → ℤ) : Prop where
  certificate :
    ∀ {s k}, introducedLabel L n S J s k →
      LabelExponentCertificate L n S J s k (t s k) (numerator s k) (leastValue s k)

/-- Supplied corrected exponent post-data for a Case 2 `J`-advance.

This packages only exponent-map bookkeeping: old introduced labels keep their
vector, numerator, and least-value data, while the new label `(S,J+1)` receives
the corrected prefix-minimum Case 2 data.  It does not assert chart production,
source comparability, or that the corrected vector is the PDF's printed vector. -/
structure Case2CorrectedExponentPostData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ) : Prop where
  vector_old :
    ∀ {s k}, introducedLabel L n S J s k → t' s k = t s k
  numerator_old :
    ∀ {s k}, introducedLabel L n S J s k → numerator' s k = numerator s k
  leastValue_old :
    ∀ {s k}, introducedLabel L n S J s k → leastValue' s k = leastValue s k
  vector_new : t' S (J + 1) = correctedCase2PivotVector n S J
  numerator_new :
    numerator' S (J + 1) =
      ((prefixMinNat n S : ℤ) - (J : ℤ)) * ((n (S + 1) : ℤ) - (J : ℤ))
  leastValue_new : leastValue' S (J + 1) = (J : ℤ)

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

namespace IntroducedLabelExponentCertificates

/-- Domain-extension bookkeeping from supplied corrected Case 2 exponent
post-data.  The corrected new-label certificate supplies only the new label;
the post-data supplies preservation of the old exponent maps and the explicit
new corrected exponent values. -/
theorem extendDomain_correctedCase2NewLabel_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (hpost :
      Case2CorrectedExponentPostData
        (L := L) (n := n) (S := S) (J := J)
        t t' numerator numerator' leastValue leastValue') :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' := by
  refine hcert.extendDomain_succ_current ?_
    hpost.vector_old hpost.numerator_old hpost.leastValue_old
  rw [hpost.vector_new, hpost.numerator_new, hpost.leastValue_new]
  exact hnew.labelExponentCertificate

/-- Actual-width stage relabel for exponent certificates.

If the old `(S,J+1)` introduced-label domain agrees with the relabelled
`(S+1,0)` domain, then the same exponent maps certify the relabelled domain.
This changes only the introduced-label proof in each one-label certificate. -/
theorem relabel_currentSucc_succStage_zero_of_nextWidth_eq
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (hcert :
      IntroducedLabelExponentCertificates L n S (J + 1) t numerator leastValue)
    (hwidth : n (S + 1) = J + 1) :
    IntroducedLabelExponentCertificates L n (S + 1) 0 t numerator leastValue where
  certificate := by
    intro s k hnew
    have hold : introducedLabel L n S (J + 1) s k :=
      (introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq
        L n hwidth).2 hnew
    have hc := hcert.certificate hold
    exact
      { introduced := hnew
        terminalExponent_eq := hc.terminalExponent_eq
        least_value := hc.least_value }

end IntroducedLabelExponentCertificates

namespace Case2CorrectedExponentPostData

/-- The concrete corrected Case 2 selected-label overrides supply the corrected
exponent post-data package. -/
theorem updateSelected
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (t : ℕ → ℕ → ℕ → ℤ) (numerator leastValue : ℕ → ℕ → ℤ) :
    Case2CorrectedExponentPostData
      (L := L) (n := n) (S := S) (J := J)
      t
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      numerator
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      leastValue
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) where
  vector_old := by
    intro s k hintro
    exact funext fun i ↦ updateSelectedLabelVector_of_ne
      (correctedCase2PivotVector n S J) t i (by
        rintro ⟨rfl, rfl⟩
        exact (not_introducedLabel_case2_new_before _ _ _ _) hintro)
  numerator_old := by
    intro s k hintro
    exact updateSelectedLabelScalar_of_ne
      (((prefixMinNat n S : ℤ) - (J : ℤ)) *
        ((n (S + 1) : ℤ) - (J : ℤ))) numerator (by
        rintro ⟨rfl, rfl⟩
        exact (not_introducedLabel_case2_new_before _ _ _ _) hintro)
  leastValue_old := by
    intro s k hintro
    exact updateSelectedLabelScalar_of_ne (J : ℤ) leastValue (by
      rintro ⟨rfl, rfl⟩
      exact (not_introducedLabel_case2_new_before _ _ _ _) hintro)
  vector_new := funext fun i ↦ updateSelectedLabelVector_selected S (J + 1)
    (correctedCase2PivotVector n S J) t i
  numerator_new := updateSelectedLabelScalar_selected S (J + 1)
    (((prefixMinNat n S : ℤ) - (J : ℤ)) *
      ((n (S + 1) : ℤ) - (J : ℤ))) numerator
  leastValue_new := updateSelectedLabelScalar_selected S (J + 1) (J : ℤ) leastValue

end Case2CorrectedExponentPostData

namespace IntroducedLabelExponentCertificates

/-- Concrete update-data wrapper for corrected Case 2 exponent-domain
extension.  It changes only the new label `(S,J+1)` to the corrected
Case 2 vector, numerator, and least value, leaving all old introduced-label
exponent data unchanged.  This is domain-extension bookkeeping, not chart
production or a transition theorem. -/
theorem extendDomain_correctedCase2NewLabel_updateData_of_prefixBound
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hJcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    IntroducedLabelExponentCertificates L n S (J + 1)
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) := by
  exact hcert.extendDomain_correctedCase2NewLabel_of_postData
    (correctedCase2NewLabelCertificate_of_prefixBound L n hS hSL hJcont)
    (Case2CorrectedExponentPostData.updateSelected t numerator leastValue)

end IntroducedLabelExponentCertificates

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

/-- The source row label underlying a displayed Case 2 residual-row index. -/
def case2ResidualRowLevel
    (n : ℕ → ℕ) (S J : ℕ) (i : Case2ResidualRowIndex n S J) : ℕ :=
  i.1

/-- Candidate selected entries in the Case 2 residual-block center, not a chart cover proof. -/
def case2ResidualBlockPivotEntries (n : ℕ → ℕ) (S J : ℕ) : Finset (ℕ × ℕ) :=
  (case2ResidualBlockRows n S J).product (case2ResidualBlockCols n S J)

/-- The displayed Case 2 continuation bound implies the current prefix-minimum bound. -/
theorem case2_continuation_le_prefixMinNat_current
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    J ≤ prefixMinNat n S := by
  exact le_trans (by omega : J ≤ J + 1)
    (le_trans hcont (prefixMinNat_succ_le n hS))

/-- The displayed Case 2 continuation bound implies the next actual-width bound. -/
theorem case2_continuation_le_width_next
    (n : ℕ → ℕ) {S J : ℕ}
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    J ≤ n (S + 1) := by
  exact le_trans (by omega : J ≤ J + 1)
    (le_trans hcont (prefixMinNat_le_width n (by omega : 1 ≤ S + 1)))

/-- Cardinality of the Case 2 residual-block row range `J+1..M(S)`. -/
theorem case2ResidualBlockRows_card (n : ℕ → ℕ) (S J : ℕ) :
    (case2ResidualBlockRows n S J).card = prefixMinNat n S - J := by
  rw [case2ResidualBlockRows, Nat.card_Icc]
  omega

/-- Cardinality of the Case 2 residual-block column range `J+1..M^(S+1)`. -/
theorem case2ResidualBlockCols_card (n : ℕ → ℕ) (S J : ℕ) :
    (case2ResidualBlockCols n S J).card = n (S + 1) - J := by
  rw [case2ResidualBlockCols, Nat.card_Icc]
  omega

/-- Cardinality of the finite Case 2 residual-block selected-entry set.
This is the coordinate-equation count, not a chart coverage or Jacobian theorem. -/
theorem case2ResidualBlockPivotEntries_card (n : ℕ → ℕ) (S J : ℕ) :
    (case2ResidualBlockPivotEntries n S J).card =
      (prefixMinNat n S - J) * (n (S + 1) - J) := by
  simp [case2ResidualBlockPivotEntries, case2ResidualBlockRows_card,
    case2ResidualBlockCols_card]

/-- Corrected Case 2 new-label numerator expression as integer arithmetic data.
It is the selected coordinate-equation count under the displayed continuation
bounds; it is not a chart-produced exponent update or a Jacobian exponent. -/
def correctedCase2NewLabelNumerator (n : ℕ → ℕ) (S J : ℕ) : ℤ :=
  ((prefixMinNat n S : ℤ) - (J : ℤ)) * ((n (S + 1) : ℤ) - (J : ℤ))

/-- Under explicit interval bounds, the corrected Case 2 numerator is the
integer cardinality of the residual-block selected-entry set. -/
theorem correctedCase2NewLabelNumerator_eq_card_of_bounds
    (n : ℕ → ℕ) {S J : ℕ}
    (hrow : J ≤ prefixMinNat n S) (hcol : J ≤ n (S + 1)) :
    correctedCase2NewLabelNumerator n S J =
      ((case2ResidualBlockPivotEntries n S J).card : ℤ) := by
  rw [correctedCase2NewLabelNumerator,
    case2ResidualBlockPivotEntries_card, Nat.cast_mul,
    Nat.cast_sub hrow, Nat.cast_sub hcol]

/-- Under displayed Case 2 continuation, the corrected numerator is the
integer count of selected residual-block coordinates. -/
theorem correctedCase2NewLabelNumerator_eq_card_of_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    correctedCase2NewLabelNumerator n S J =
      ((case2ResidualBlockPivotEntries n S J).card : ℤ) := by
  exact correctedCase2NewLabelNumerator_eq_card_of_bounds n
    (case2_continuation_le_prefixMinNat_current n hS hcont)
    (case2_continuation_le_width_next n hcont)

namespace Case2CorrectedExponentPostData

/-- Supplied corrected Case 2 exponent post-data assigns the new label the
corrected numerator expression.  This is bookkeeping, not chart production. -/
theorem numerator_new_eq_correctedNumerator
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hpost :
      Case2CorrectedExponentPostData
        (L := L) (n := n) (S := S) (J := J)
        t t' numerator numerator' leastValue leastValue') :
    numerator' S (J + 1) = correctedCase2NewLabelNumerator n S J := by
  simpa [correctedCase2NewLabelNumerator] using hpost.numerator_new

/-- Under displayed continuation, supplied corrected Case 2 exponent post-data
assigns the new label the selected residual-block coordinate count. -/
theorem numerator_new_eq_card_of_cont
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hpost :
      Case2CorrectedExponentPostData
        (L := L) (n := n) (S := S) (J := J)
        t t' numerator numerator' leastValue leastValue') :
    numerator' S (J + 1) = ((case2ResidualBlockPivotEntries n S J).card : ℤ) := by
  exact hpost.numerator_new_eq_correctedNumerator.trans
    (correctedCase2NewLabelNumerator_eq_card_of_cont n hS hcont)

end Case2CorrectedExponentPostData

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

/-- Row subtype extracted from a finite Case 2 residual-block pivot entry. -/
def case2ResidualBlockPivotRowOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J) :
    Case2ResidualRowIndex n S J :=
  ⟨p.1, by
    rcases p with ⟨i, j⟩
    rw [mem_case2ResidualBlockPivotEntries_iff] at hp
    rw [mem_case2ResidualBlockRows]
    exact ⟨hp.1, hp.2.1⟩⟩

/-- Column subtype extracted from a finite Case 2 residual-block pivot entry. -/
def case2ResidualBlockPivotColOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J) :
    Case2ResidualColIndex n S J :=
  ⟨p.2, by
    rcases p with ⟨i, j⟩
    rw [mem_case2ResidualBlockPivotEntries_iff] at hp
    rw [mem_case2ResidualBlockCols]
    exact ⟨hp.2.2.1, hp.2.2.2⟩⟩

@[simp] theorem case2ResidualBlockPivotRowOfMem_val
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J) :
    (case2ResidualBlockPivotRowOfMem hp).1 = p.1 :=
  rfl

@[simp] theorem case2ResidualBlockPivotColOfMem_val
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J) :
    (case2ResidualBlockPivotColOfMem hp).1 = p.2 :=
  rfl

@[simp] theorem case2ResidualBlockPivotOfMem_pair
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J) :
    ((case2ResidualBlockPivotRowOfMem hp).1,
      (case2ResidualBlockPivotColOfMem hp).1) = p := by
  rcases p with ⟨i, j⟩
  rfl

/-- Every displayed Case 2 residual-row level is at or below the current pivot tail. -/
theorem case2ResidualRowLevel_ge
    (n : ℕ → ℕ) (S J : ℕ) (i : Case2ResidualRowIndex n S J) :
    J + 1 ≤ case2ResidualRowLevel n S J i :=
  ((mem_case2ResidualBlockRows n S J i.1).mp i.2).1

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

/-- The displayed Case 2 pivot row has source row level `J+1`. -/
@[simp] theorem case2ResidualRowLevel_displayedPivotRow
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    case2ResidualRowLevel n S J (case2DisplayedPivotRow n hS hcont) = J + 1 :=
  rfl

/-- The displayed Case 2 pivot column `J+1`, as an element of the residual-column index type. -/
def case2DisplayedPivotCol
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    Case2ResidualColIndex n S J :=
  ⟨J + 1, by
    rw [mem_case2ResidualBlockCols]
    exact ⟨le_rfl,
      le_trans hcont (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))⟩⟩

/-- Residual Case 2 rows left after the displayed pivot at `(J+1,J+1)` is
removed.  This is only a finite lower-right domain, not an advance
transition. -/
def case2PostPivotRows (n : ℕ → ℕ) (S J : ℕ) : Finset ℕ :=
  Finset.Icc (J + 2) (prefixMinNat n S)

/-- Residual Case 2 columns left after the displayed pivot at `(J+1,J+1)` is
removed.  Columns still use the actual next width. -/
def case2PostPivotCols (n : ℕ → ℕ) (S J : ℕ) : Finset ℕ :=
  Finset.Icc (J + 2) (n (S + 1))

/-- Lower-right residual block entries left after the displayed Case 2 pivot.
This records the finite domain for the next possible `J`-advance. -/
def case2PostPivotEntries (n : ℕ → ℕ) (S J : ℕ) : Finset (ℕ × ℕ) :=
  (case2PostPivotRows n S J).product (case2PostPivotCols n S J)

/-- The post-pivot row domain is exactly the next same-stage Case 2 residual
row domain.  This is finite-domain bookkeeping, not a transition theorem. -/
theorem case2PostPivotRows_eq_case2ResidualBlockRows_succ
    (n : ℕ → ℕ) (S J : ℕ) :
    case2PostPivotRows n S J = case2ResidualBlockRows n S (J + 1) :=
  rfl

/-- The post-pivot column domain is exactly the next same-stage Case 2 residual
column domain.  This is finite-domain bookkeeping, not a transition theorem. -/
theorem case2PostPivotCols_eq_case2ResidualBlockCols_succ
    (n : ℕ → ℕ) (S J : ℕ) :
    case2PostPivotCols n S J = case2ResidualBlockCols n S (J + 1) :=
  rfl

/-- The post-pivot entry domain is exactly the next same-stage Case 2 residual
center domain.  This is finite-domain bookkeeping, not chart production. -/
theorem case2PostPivotEntries_eq_case2ResidualBlockPivotEntries_succ
    (n : ℕ → ℕ) (S J : ℕ) :
    case2PostPivotEntries n S J = case2ResidualBlockPivotEntries n S (J + 1) :=
  rfl

@[simp] theorem mem_case2PostPivotRows (n : ℕ → ℕ) (S J i : ℕ) :
    i ∈ case2PostPivotRows n S J ↔ J + 2 ≤ i ∧ i ≤ prefixMinNat n S := by
  simp [case2PostPivotRows, Finset.mem_Icc]

@[simp] theorem mem_case2PostPivotCols (n : ℕ → ℕ) (S J j : ℕ) :
    j ∈ case2PostPivotCols n S J ↔ J + 2 ≤ j ∧ j ≤ n (S + 1) := by
  simp [case2PostPivotCols, Finset.mem_Icc]

@[simp] theorem mem_case2PostPivotEntries_iff (n : ℕ → ℕ) (S J i j : ℕ) :
    (i, j) ∈ case2PostPivotEntries n S J ↔
      J + 2 ≤ i ∧ i ≤ prefixMinNat n S ∧ J + 2 ≤ j ∧ j ≤ n (S + 1) := by
  simp [case2PostPivotEntries, and_assoc]

theorem case2PostPivotRows_card (n : ℕ → ℕ) (S J : ℕ) :
    (case2PostPivotRows n S J).card = prefixMinNat n S - (J + 1) := by
  rw [case2PostPivotRows, Nat.card_Icc]
  omega

theorem case2PostPivotCols_card (n : ℕ → ℕ) (S J : ℕ) :
    (case2PostPivotCols n S J).card = n (S + 1) - (J + 1) := by
  rw [case2PostPivotCols, Nat.card_Icc]
  omega

theorem case2PostPivotEntries_card (n : ℕ → ℕ) (S J : ℕ) :
    (case2PostPivotEntries n S J).card =
      (prefixMinNat n S - (J + 1)) * (n (S + 1) - (J + 1)) := by
  simp [case2PostPivotEntries, case2PostPivotRows_card,
    case2PostPivotCols_card]

theorem case2PostPivotRows_nonempty_iff (n : ℕ → ℕ) (S J : ℕ) :
    (case2PostPivotRows n S J).Nonempty ↔ J + 2 ≤ prefixMinNat n S := by
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_case2PostPivotRows] at hi
    omega
  · intro h
    exact ⟨J + 2, by rw [mem_case2PostPivotRows]; omega⟩

theorem case2PostPivotCols_nonempty_iff (n : ℕ → ℕ) (S J : ℕ) :
    (case2PostPivotCols n S J).Nonempty ↔ J + 2 ≤ n (S + 1) := by
  constructor
  · rintro ⟨j, hj⟩
    rw [mem_case2PostPivotCols] at hj
    omega
  · intro h
    exact ⟨J + 2, by rw [mem_case2PostPivotCols]; omega⟩

/-- The lower-right post-pivot Case 2 block is nonempty exactly when the next
Case 2 continuation bound holds, in the old `(S,J)` notation. -/
theorem case2PostPivotEntries_nonempty_iff_next_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S) :
    (case2PostPivotEntries n S J).Nonempty ↔
      J + 2 ≤ prefixMinNat n (S + 1) := by
  constructor
  · rintro ⟨p, hp⟩
    rcases p with ⟨i, j⟩
    rw [mem_case2PostPivotEntries_iff] at hp
    rw [prefixMinNat_succ_eq_min n hS]
    exact le_min (le_trans hp.1 hp.2.1) (le_trans hp.2.2.1 hp.2.2.2)
  · intro hnext
    have hrow : J + 2 ≤ prefixMinNat n S :=
      le_trans hnext (prefixMinNat_succ_le n hS)
    have hcol : J + 2 ≤ n (S + 1) :=
      le_trans hnext (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))
    refine ⟨(J + 2, J + 2), ?_⟩
    rw [mem_case2PostPivotEntries_iff]
    exact ⟨le_rfl, hrow, le_rfl, hcol⟩

/-- The next same-stage Case 2 residual center is nonempty exactly under the
next continuation bound.

This is the same finite-domain fact as
`case2PostPivotEntries_nonempty_iff_next_cont`, rewritten after the
post-pivot/next-residual handoff. -/
theorem case2ResidualBlockPivotEntries_succ_nonempty_iff_next_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S) :
    (case2ResidualBlockPivotEntries n S (J + 1)).Nonempty ↔
      J + 2 ≤ prefixMinNat n (S + 1) := by
  rw [← case2PostPivotEntries_eq_case2ResidualBlockPivotEntries_succ n S J]
  exact case2PostPivotEntries_nonempty_iff_next_cont n hS

theorem case2PostPivotRows_eq_empty_of_le
    {n : ℕ → ℕ} {S J : ℕ} (h : prefixMinNat n S ≤ J + 1) :
    case2PostPivotRows n S J = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  rw [mem_case2PostPivotRows] at hi
  omega

theorem case2PostPivotCols_eq_empty_of_le
    {n : ℕ → ℕ} {S J : ℕ} (h : n (S + 1) ≤ J + 1) :
    case2PostPivotCols n S J = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  rw [mem_case2PostPivotCols] at hj
  omega

theorem case2PostPivotRows_eq_empty_of_prefixMin_current_eq
    {n : ℕ → ℕ} {S J : ℕ} (h : prefixMinNat n S = J + 1) :
    case2PostPivotRows n S J = ∅ :=
  case2PostPivotRows_eq_empty_of_le (by omega)

/-- Current-prefix row exhaustion forces the next displayed Case 2
continuation bound to fail.

This is the row-exhausted terminal side.  It does not assert actual next-width
exhaustion, so it does not empty the post-pivot column range. -/
theorem case2_not_next_cont_of_prefixMin_current_eq
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hrow : prefixMinNat n S = J + 1) :
    ¬ J + 2 ≤ prefixMinNat n (S + 1) := by
  intro hnext
  have hle : prefixMinNat n (S + 1) ≤ J + 1 := by
    exact le_trans (prefixMinNat_succ_le n hS) (by omega)
  omega

theorem case2PostPivotCols_eq_empty_of_width_next_eq
    {n : ℕ → ℕ} {S J : ℕ} (h : n (S + 1) = J + 1) :
    case2PostPivotCols n S J = ∅ :=
  case2PostPivotCols_eq_empty_of_le (by omega)

/-- If the displayed pivot was valid but the next pivot is not, then the
frontier prefix minimum is exactly `J+1`.  This is off-by-one bookkeeping for
the post-pivot domain, not a termination theorem. -/
theorem case2_next_frontier_eq_of_cont_of_not_next
    {n : ℕ → ℕ} {S J : ℕ}
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1)) :
    prefixMinNat n (S + 1) = J + 1 := by
  omega

/-- If the current displayed Case 2 pivot is valid but the next one is not,
then the exhausted frontier comes from the current prefix row side or from the
actual next-width column side.  The disjunction need not be exclusive. -/
theorem case2_next_frontier_currentPrefixMin_or_nextWidth_eq_of_cont_of_not_next
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1)) :
    prefixMinNat n S = J + 1 ∨ n (S + 1) = J + 1 := by
  have hfront : prefixMinNat n (S + 1) = J + 1 :=
    case2_next_frontier_eq_of_cont_of_not_next hcont hstop
  have hfront_min : min (prefixMinNat n S) (n (S + 1)) = J + 1 := by
    simpa [prefixMinNat_succ_eq_min n hS] using hfront
  by_cases hle : prefixMinNat n S ≤ n (S + 1)
  · exact Or.inl (by simpa [Nat.min_eq_left hle] using hfront_min)
  · have hle' : n (S + 1) ≤ prefixMinNat n S := by omega
    exact Or.inr (by simpa [Nat.min_eq_right hle'] using hfront_min)

/-- If the next Case 2 continuation bound fails after the displayed pivot, then
at least one lower-right post-pivot side is empty.  This is only a finite
domain-exhaustion statement. -/
theorem case2PostPivotRows_empty_or_cols_empty_of_not_next_cont
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1)) :
    case2PostPivotRows n S J = ∅ ∨ case2PostPivotCols n S J = ∅ := by
  have hlt : prefixMinNat n (S + 1) < J + 2 := Nat.lt_of_not_ge hstop
  have hmin_le_raw : prefixMinNat n (S + 1) ≤ J + 1 := by omega
  have hmin_le : min (prefixMinNat n S) (n (S + 1)) ≤ J + 1 := by
    simpa [prefixMinNat_succ_eq_min n hS] using hmin_le_raw
  by_cases hrow : prefixMinNat n S ≤ J + 1
  · exact Or.inl (case2PostPivotRows_eq_empty_of_le hrow)
  · have hcol : n (S + 1) ≤ J + 1 := by
      by_cases hle : prefixMinNat n S ≤ n (S + 1)
      · have hmu : prefixMinNat n S ≤ J + 1 := by
          simpa [Nat.min_eq_left hle] using hmin_le
        exact False.elim (hrow hmu)
      · have hle' : n (S + 1) ≤ prefixMinNat n S := by omega
        simpa [Nat.min_eq_right hle'] using hmin_le
    exact Or.inr (case2PostPivotCols_eq_empty_of_le hcol)

/-- Failure of the next Case 2 continuation bound empties the lower-right
post-pivot residual entry set. -/
theorem case2PostPivotEntries_eq_empty_of_not_next_cont
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1)) :
    case2PostPivotEntries n S J = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  exact hstop ((case2PostPivotEntries_nonempty_iff_next_cont n hS).1 ⟨p, hp⟩)

/-- A supplied finite frontier branch after the displayed Case 2 pivot.

The stopped constructors are not mutually exclusive: the current-prefix row
side and actual next-width column side may both be exhausted.  This is only
finite domain bookkeeping, not a chart-transition or terminal-source theorem. -/
inductive Case2DisplayedStepBranch (n : ℕ → ℕ) (S J : ℕ) : Prop where
  | continuing (hnext : J + 2 ≤ prefixMinNat n (S + 1))
  | actualWidthStopped (hwidth : n (S + 1) = J + 1)
  | rowExhaustedStopped (hrow : prefixMinNat n S = J + 1)

/-- A valid displayed Case 2 pivot gives the overlapping finite frontier
alternatives: either the next same-stage residual center is nonempty, or one
of the two stopped sides has frontier value `J+1`.

This is only the arithmetic frontier split.  It does not assert chart coverage,
source-produced post-data, terminal relabeling outside the actual-width branch,
or any normal-crossing/RLCT consequence. -/
theorem case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    J + 2 ≤ prefixMinNat n (S + 1) ∨
      n (S + 1) = J + 1 ∨ prefixMinNat n S = J + 1 := by
  by_cases hnext : J + 2 ≤ prefixMinNat n (S + 1)
  · exact Or.inl hnext
  · rcases
      case2_next_frontier_currentPrefixMin_or_nextWidth_eq_of_cont_of_not_next
        hS hcont hnext with hrow | hwidth
    · exact Or.inr (Or.inr hrow)
    · exact Or.inr (Or.inl hwidth)

/-- Choose a finite frontier branch from the current displayed Case 2 pivot
validity.  The choice is only a witness for downstream case analysis; it does
not make the stopped constructors exclusive. -/
theorem case2DisplayedStepBranch_of_cont
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    Case2DisplayedStepBranch n S J := by
  rcases
      case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont
        hS hcont with hnext | hstop
  · exact Case2DisplayedStepBranch.continuing hnext
  · rcases hstop with hwidth | hrow
    · exact Case2DisplayedStepBranch.actualWidthStopped hwidth
    · exact Case2DisplayedStepBranch.rowExhaustedStopped hrow

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

/-- The Case 1 first-jump row bound plus the actual column bound gives the
displayed top-left pivot continuation bound `J+1 <= mu_(S+1)`.

This is finite width bookkeeping for the displayed pivot, not a transition
theorem or a proof that the state continues rather than later advances. -/
theorem Case1FirstJumpHypotheses.continuationBound_of_colBound
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (h : Case1FirstJumpHypotheses L n S J J1 s k level vector)
    (hS : 1 ≤ S) (hcol : J + 1 ≤ n (S + 1)) :
    J + 1 ≤ prefixMinNat n (S + 1) := by
  rw [prefixMinNat_succ_eq_min n hS]
  exact le_min (le_trans (Nat.add_le_add_left h.positive J) h.rowBound) hcol

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

section SelectedEntryWeightedMatrix

variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ] [CommSemiring α]

/-- Row-weighted selected-entry substitution factors the selected variable into the
row diagonal. This is finite algebra only, not a chart construction. -/
theorem diagonal_mul_selectedEntrySubstitutionMatrix
    (rowPivot : ι) (colPivot : κ) (u : α) (weight : ι → α)
    (residual : ι → κ → α) :
    diagonal weight * selectedEntrySubstitutionMatrix rowPivot colPivot u residual =
      diagonal (fun i ↦ u * weight i) *
        selectedEntryNormalizedMatrix rowPivot colPivot residual := by
  ext i j
  simp [selectedEntrySubstitutionMatrix_eq_mul_normalized]
  ac_rfl

end SelectedEntryWeightedMatrix

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

/-- In a selected-generator chart, the ideal generated by the transformed
finite center is exactly the principal ideal generated by the selected
variable.  This is finite ideal algebra only, not a chart-coverage or
regularity theorem. -/
theorem selectedEntryChartMap_centerIdeal_eq_span_singleton
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    {center : Finset ι} {pivot : ι} (hpivot : pivot ∈ center)
    (u : R) (residual : ι → R) :
    Ideal.span
        {v : R | ∃ i, i ∈ center ∧ selectedEntryChartMap pivot u residual i = v} =
      Ideal.span ({u} : Set R) := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    intro v hv
    rcases hv with ⟨i, _hi, hval⟩
    rw [← hval]
    rcases selectedEntryChartMap_pivot_dvd pivot u residual i with ⟨w, hw⟩
    rw [hw]
    exact (Ideal.span ({u} : Set R)).mul_mem_right w
      (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    intro v hv
    rcases hv with rfl
    exact Ideal.subset_span ⟨pivot, hpivot, by simp⟩

/-- Case 2 specialization: in a supplied residual-block selected-entry chart,
the pulled-back finite center ideal is generated by the selected variable. -/
theorem case2_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem
    {n : ℕ → ℕ} {S J : ℕ} {pivot : ℕ × ℕ}
    (hpivot : pivot ∈ case2ResidualBlockPivotEntries n S J)
    {R : Type*} [CommSemiring R] (u : R) (residual : ℕ × ℕ → R) :
    Ideal.span
        {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
          selectedEntryChartMap pivot u residual p = v} =
      Ideal.span ({u} : Set R) :=
  selectedEntryChartMap_centerIdeal_eq_span_singleton hpivot u residual

/-- Case 1 specialization: in a supplied selected-generator chart for the
finite Case 1 center, the pulled-back finite center ideal is generated by the
selected variable. -/
theorem case1_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem
    {n : ℕ → ℕ} {S J J1 : ℕ} {pivot : Case1CenterGenerator}
    (hpivot : pivot ∈ case1CenterGenerators n S J J1)
    {R : Type*} [CommSemiring R] (u : R) (residual : Case1CenterGenerator → R) :
    Ideal.span
        {v : R | ∃ g, g ∈ case1CenterGenerators n S J J1 ∧
          selectedEntryChartMap pivot u residual g = v} =
      Ideal.span ({u} : Set R) :=
  selectedEntryChartMap_centerIdeal_eq_span_singleton hpivot u residual

/-- The finite Case 1 center is nonempty, witnessed by the externally chosen
old exceptional generator. This is finite center bookkeeping, not a source
validity theorem for the hidden old label. -/
theorem case1CenterGenerators_nonempty
    (n : ℕ → ℕ) (S J J1 : ℕ) :
    (case1CenterGenerators n S J J1).Nonempty :=
  ⟨(Sum.inl () : Case1CenterGenerator), case1_selectedOld_mem_center n S J J1⟩

/-- Under the displayed Case 1 entry bounds, the row-strip part of the center
is nonempty, witnessed by the top-left strip entry. -/
theorem case1StripEntries_nonempty_of_bounds
    (n : ℕ → ℕ) (S : ℕ) {J J1 : ℕ}
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1)) :
    (case1StripEntries n S J J1).Nonempty :=
  ⟨(J + 1, J + 1), by
    rw [mem_case1StripEntries_iff]
    exact ⟨le_rfl, by omega, le_rfl, hcol⟩⟩

/-- A right-branch Case 1 center generator is exactly a row-strip entry. -/
theorem mem_case1CenterGenerators_inr_iff
    {n : ℕ → ℕ} {S J J1 : ℕ} {p : ℕ × ℕ} :
    (Sum.inr p : Case1CenterGenerator) ∈ case1CenterGenerators n S J J1 ↔
      p ∈ case1StripEntries n S J J1 := by
  simp [case1CenterGenerators]

/-- Assumption boundary for a finite selected-entry chart family.  It records
the chart-regularity and transition-regularity obligations for selected entries
in a finite center without constructing a blow-up atlas. -/
structure SelectedEntryChartFamilyBoundary
    {ι : Type*} (center : Finset ι)
    (ChartRegular : ι → Prop)
    (TransitionRegular : ι → ι → Prop) : Prop where
  chart_regular_of_mem :
    ∀ {p}, p ∈ center → ChartRegular p
  transition_regular_of_mem :
    ∀ {p}, p ∈ center → ∀ {q}, q ∈ center → TransitionRegular p q

/-- Case 1 instance of the selected-entry chart-family assumption boundary.
The `Unit` branch is the externally selected old exceptional generator, and
the right branch is the finite row strip.  This names regularity obligations
for the finite center; it is not a proof of chart coverage or a source-order
transition formula. -/
abbrev Case1CenterChartFamilyBoundary
    (n : ℕ → ℕ) (S J J1 : ℕ)
    (ChartRegular : Case1CenterGenerator → Prop)
    (TransitionRegular :
      Case1CenterGenerator → Case1CenterGenerator → Prop) : Prop :=
  SelectedEntryChartFamilyBoundary
    (case1CenterGenerators n S J J1) ChartRegular TransitionRegular

namespace Case1CenterChartFamilyBoundary

/-- A Case 1 center chart-family boundary supplies chart regularity for every
supplied generator in the finite Case 1 center. -/
theorem chart_regular_of_mem
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (h : Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular)
    {g : Case1CenterGenerator} (hg : g ∈ case1CenterGenerators n S J J1) :
    ChartRegular g :=
  SelectedEntryChartFamilyBoundary.chart_regular_of_mem h hg

/-- A Case 1 center chart-family boundary supplies transition regularity for
every pair of supplied generators in the finite Case 1 center. -/
theorem transition_regular_of_mem
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (h : Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular)
    {g hgen : Case1CenterGenerator}
    (hg : g ∈ case1CenterGenerators n S J J1)
    (hh : hgen ∈ case1CenterGenerators n S J J1) :
    TransitionRegular g hgen :=
  SelectedEntryChartFamilyBoundary.transition_regular_of_mem h hg hh

/-- A Case 1 center chart-family boundary supplies chart regularity for the
selected old-exceptional-variable chart.  The source validity of the hidden
old label is still external to the `Unit` generator. -/
theorem chart_regular_selectedOld
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (h : Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular) :
    ChartRegular (Sum.inl () : Case1CenterGenerator) :=
  SelectedEntryChartFamilyBoundary.chart_regular_of_mem h
    (case1_selectedOld_mem_center n S J J1)

/-- Under the displayed Case 1 entry bounds, a Case 1 center chart-family
boundary supplies chart regularity for Aoyagi's top-left row-strip pivot. -/
theorem chart_regular_displayedPivot_of_bounds
    {n : ℕ → ℕ} {S J J1 : ℕ}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (h : Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular)
    (hJ1 : 1 ≤ J1) (hcol : J + 1 ≤ n (S + 1)) :
    ChartRegular (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) :=
  SelectedEntryChartFamilyBoundary.chart_regular_of_mem h
    (case1_displayedPivot_mem_center_of_bounds n S hJ1 hcol)

/-- The first-jump package supplies the displayed Case 1 row-strip pivot
positivity hypothesis, but the source column bound remains explicit. -/
theorem chart_regular_displayedPivot_of_firstJump_colBound
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (h : Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s k level vector)
    (hcol : J + 1 ≤ n (S + 1)) :
    ChartRegular (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) :=
  chart_regular_displayedPivot_of_bounds h hfirst.positive hcol

end Case1CenterChartFamilyBoundary

/-- Case 2 residual-block instance of the selected-entry chart-family
assumption boundary.  This names the remaining chart-family regularity
interface; it is not a proof of an affine blow-up atlas. -/
abbrev Case2ResidualBlockChartFamilyBoundary
    (n : ℕ → ℕ) (S J : ℕ)
    (ChartRegular : ℕ × ℕ → Prop)
    (TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop) : Prop :=
  SelectedEntryChartFamilyBoundary
    (case2ResidualBlockPivotEntries n S J) ChartRegular TransitionRegular

/-- The Case 2 residual-block pivot-entry set is nonempty under the same
continuation hypothesis that makes the displayed top-left pivot source-valid. -/
theorem case2ResidualBlockPivotEntries_nonempty_of_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    (case2ResidualBlockPivotEntries n S J).Nonempty :=
  ⟨(J + 1, J + 1),
    case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont⟩

namespace Case2ResidualBlockChartFamilyBoundary

/-- A Case 2 residual-block chart-family boundary supplies chart regularity for
every supplied source pivot pair in the finite residual-block center. -/
theorem chart_regular_of_mem
    {n : ℕ → ℕ} {S J : ℕ}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (h :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    {p : ℕ × ℕ} (hp : p ∈ case2ResidualBlockPivotEntries n S J) :
    ChartRegular p :=
  SelectedEntryChartFamilyBoundary.chart_regular_of_mem h hp

/-- A Case 2 residual-block chart-family boundary supplies transition
regularity for every pair of supplied source pivot entries in the finite
residual-block center. -/
theorem transition_regular_of_mem
    {n : ℕ → ℕ} {S J : ℕ}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (h :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    {p q : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (hq : q ∈ case2ResidualBlockPivotEntries n S J) :
    TransitionRegular p q :=
  SelectedEntryChartFamilyBoundary.transition_regular_of_mem h hp hq

/-- Under continuation, a Case 2 residual-block chart-family boundary supplies
regularity for Aoyagi's displayed top-left pivot chart. -/
theorem chart_regular_displayedPivot_of_cont
    {n : ℕ → ℕ} {S J : ℕ}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (h :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    ChartRegular (J + 1, J + 1) :=
  SelectedEntryChartFamilyBoundary.chart_regular_of_mem h
    (case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont)

end Case2ResidualBlockChartFamilyBoundary

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

/-- Conditional bridge between Nat-valued source levels and integer least values
for labels introduced at a state. -/
structure IntroducedLabelLevelInvariants
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (level : ℕ → ℕ → ℕ) (leastValue : ℕ → ℕ → ℤ) : Prop where
  leastValue_eq_level :
    ∀ {s k}, introducedLabel L n S J s k → leastValue s k = (level s k : ℤ)

namespace IntroducedLabelLevelInvariants

/-- Actual-width stage relabel for the `leastValue = level` bridge. -/
theorem relabel_currentSucc_succStage_zero_of_nextWidth_eq
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {level : ℕ → ℕ → ℕ} {leastValue : ℕ → ℕ → ℤ}
    (hinv : IntroducedLabelLevelInvariants L n S (J + 1) level leastValue)
    (hwidth : n (S + 1) = J + 1) :
    IntroducedLabelLevelInvariants L n (S + 1) 0 level leastValue where
  leastValue_eq_level := by
    intro s k hnew
    exact hinv.leastValue_eq_level
      ((introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq
        L n hwidth).2 hnew)

end IntroducedLabelLevelInvariants

/-- Conditional level and above-pivot flat-tail bridges for labels introduced at a state. -/
structure IntroducedLabelLevelTailInvariants
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (level : ℕ → ℕ → ℕ)
    (t : ℕ → ℕ → ℕ → ℤ) (leastValue : ℕ → ℕ → ℤ) : Prop
    extends IntroducedLabelLevelInvariants L n S J level leastValue where
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

/-- Supplied exponent post-data for Aoyagi Case 1(1)'s selected-old chart.

The selected old label stays in the same introduced-label domain and receives
the lower-tail vector, the printed actual-width numerator increment, and least
value `J`.  Every other introduced label is supplied unchanged.  This is only
same-domain exponent bookkeeping; it does not construct the selected-old chart
or prove that coordinates produce these post-data. -/
structure Case1SelectedOldLowerTailExponentPostData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ) : Prop where
  vector_selected : t' s0 k0 = lowerTailVector (t s0 k0) S (J : ℤ)
  numerator_selected :
    numerator' s0 k0 =
      numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))
  leastValue_selected : leastValue' s0 k0 = (J : ℤ)
  vector_old :
    ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
      t' s k = t s k
  numerator_old :
    ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
      numerator' s k = numerator s k
  leastValue_old :
    ∀ {s k}, introducedLabel L n S J s k → ¬ (s = s0 ∧ k = k0) →
      leastValue' s k = leastValue s k

namespace IntroducedLabelExponentCertificates

/-- Case 1(1) same-domain selected-old lower-tail certificate update from
supplied post-data. -/
theorem case1_selectedLowerTail_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hlevelLeast : leastValue s0 k0 = (level s0 k0 : ℤ))
    (hflat : FlatTailFromPred L S (t s0 k0) (level s0 k0 : ℤ))
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (hpost :
      Case1SelectedOldLowerTailExponentPostData
        (L := L) (n := n) (S := S) (J := J) (J1 := J1) (s0 := s0) (k0 := k0)
        t t' numerator numerator' leastValue leastValue') :
    IntroducedLabelExponentCertificates L n S J t' numerator' leastValue' :=
  hcert.case1_selectedLowerTail_sameDomain hfirst hlevelLeast hflat hS hSL
    hpost.vector_selected hpost.numerator_selected hpost.leastValue_selected
    hpost.vector_old hpost.numerator_old hpost.leastValue_old

/-- Level/tail invariant wrapper for the supplied Case 1(1) same-domain
selected-old lower-tail post-data. -/
theorem case1_selectedLowerTail_of_levelTailInvariants_postData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hinv : IntroducedLabelLevelTailInvariants L n S J level t leastValue)
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (hpost :
      Case1SelectedOldLowerTailExponentPostData
        (L := L) (n := n) (S := S) (J := J) (J1 := J1) (s0 := s0) (k0 := k0)
        t t' numerator numerator' leastValue leastValue') :
    IntroducedLabelExponentCertificates L n S J t' numerator' leastValue' :=
  hcert.case1_selectedLowerTail_of_postData hfirst
    (hinv.leastValue_eq_level hfirst.selectedIntroduced)
    (hinv.flatTail_abovePivot hfirst.selectedIntroduced hfirst.lt_selectedLevel)
    hS hSL hpost

end IntroducedLabelExponentCertificates

/-- Case 1(2) displayed row-strip new-label certificate from the old selected
label.  This changes only the label identity from the old selected label to the
new post-state label `(S,J+1)`; the lower-tail arithmetic is the same
conditional certificate proved for the old vector.

The source proof that Aoyagi's displayed chart produces these post-data is a
separate obligation. -/
theorem Case1FirstJumpHypotheses.displayedRowStrip_newLabelExponentCertificate
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ} {t : ℕ → ℕ → ℕ → ℤ} {numerator : ℤ}
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hcert :
      LabelExponentCertificate L n S J s0 k0 (t s0 k0) numerator
        (level s0 k0 : ℤ))
    (hflat : FlatTailFromPred L S (t s0 k0) (level s0 k0 : ℤ))
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (hcol : J + 1 ≤ n (S + 1)) :
    LabelExponentCertificate L n S (J + 1) S (J + 1)
      (lowerTailVector (t s0 k0) S (J : ℤ))
      (numerator + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) (J : ℤ) := by
  have htail :=
    hfirst.lowerTailVector_labelExponentCertificate hcert hflat hS hSL
  exact
    { introduced :=
        introducedLabel_case2_new_after L n (by omega : 1 ≤ S) hSL hcol
      terminalExponent_eq := htail.terminalExponent_eq
      least_value := htail.least_value }

/-- Supplied exponent post-data for Aoyagi Case 1(2)'s displayed row-strip
new label.  Old introduced labels are preserved, while the fresh label
`(S,J+1)` receives the lower-tail vector of the old selected label and the
printed increment `J1 * (n(S+1)-J)`.

This is exponent-map bookkeeping only.  It does not assert chart production,
regularity, recurrence production, Jacobian accounting, or normal crossings. -/
structure Case1DisplayedRowStripExponentPostData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ) : Prop where
  vector_old :
    ∀ {s k}, introducedLabel L n S J s k → t' s k = t s k
  numerator_old :
    ∀ {s k}, introducedLabel L n S J s k → numerator' s k = numerator s k
  leastValue_old :
    ∀ {s k}, introducedLabel L n S J s k → leastValue' s k = leastValue s k
  vector_new : t' S (J + 1) = lowerTailVector (t s0 k0) S (J : ℤ)
  numerator_new :
    numerator' S (J + 1) =
      numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))
  leastValue_new : leastValue' S (J + 1) = (J : ℤ)

namespace IntroducedLabelExponentCertificates

/-- Domain-extension bookkeeping from supplied Case 1(2) displayed row-strip
new-label post-data.  The selected old certificate and flat-tail invariant
provide the elementary lower-tail certificate for the new label; the post-data
supplies preservation of all previously introduced labels and the explicit new
values. -/
theorem extendDomain_case1DisplayedRowStripNewLabel_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ} {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hlevelLeast : leastValue s0 k0 = (level s0 k0 : ℤ))
    (hflat : FlatTailFromPred L S (t s0 k0) (level s0 k0 : ℤ))
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (hcol : J + 1 ≤ n (S + 1))
    (hpost :
      Case1DisplayedRowStripExponentPostData
        (L := L) (n := n) (S := S) (J := J) (J1 := J1) (s0 := s0) (k0 := k0)
        t t' numerator numerator' leastValue leastValue') :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' := by
  refine hcert.extendDomain_succ_current ?_
    hpost.vector_old hpost.numerator_old hpost.leastValue_old
  have hselectedCert :
      LabelExponentCertificate L n S J s0 k0 (t s0 k0) (numerator s0 k0)
        (level s0 k0 : ℤ) := by
    simpa [hlevelLeast] using hcert.certificate hfirst.selectedIntroduced
  have hnew :=
    hfirst.displayedRowStrip_newLabelExponentCertificate
      hselectedCert hflat hS hSL hcol
  rw [hpost.vector_new, hpost.numerator_new, hpost.leastValue_new]
  exact hnew

end IntroducedLabelExponentCertificates

namespace Case1DisplayedRowStripExponentPostData

/-- Concrete update data for the Case 1(2) displayed row-strip new label.  It
updates only the fresh label `(S,J+1)`, which is not in the previous introduced
domain. -/
theorem updateNewLabel
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    (t : ℕ → ℕ → ℕ → ℤ) (numerator leastValue : ℕ → ℕ → ℤ) :
    Case1DisplayedRowStripExponentPostData
      (L := L) (n := n) (S := S) (J := J) (J1 := J1) (s0 := s0) (k0 := k0)
      t
      (updateSelectedLabelVector S (J + 1) (lowerTailVector (t s0 k0) S (J : ℤ)) t)
      numerator
      (updateSelectedLabelScalar S (J + 1)
        (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      leastValue
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) where
  vector_old := by
    intro s k hintro
    exact funext fun i ↦ updateSelectedLabelVector_of_ne
      (lowerTailVector (t s0 k0) S (J : ℤ)) t i (by
        rintro ⟨rfl, rfl⟩
        exact (not_introducedLabel_case2_new_before _ _ _ _) hintro)
  numerator_old := by
    intro s k hintro
    exact updateSelectedLabelScalar_of_ne
      (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator (by
        rintro ⟨rfl, rfl⟩
        exact (not_introducedLabel_case2_new_before _ _ _ _) hintro)
  leastValue_old := by
    intro s k hintro
    exact updateSelectedLabelScalar_of_ne (J : ℤ) leastValue (by
      rintro ⟨rfl, rfl⟩
      exact (not_introducedLabel_case2_new_before _ _ _ _) hintro)
  vector_new := funext fun i ↦ updateSelectedLabelVector_selected S (J + 1)
    (lowerTailVector (t s0 k0) S (J : ℤ)) t i
  numerator_new := updateSelectedLabelScalar_selected S (J + 1)
    (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator
  leastValue_new := updateSelectedLabelScalar_selected S (J + 1) (J : ℤ) leastValue

end Case1DisplayedRowStripExponentPostData

namespace IntroducedLabelExponentCertificates

/-- Concrete update-data wrapper for Case 1(2)'s displayed row-strip
new-label exponent-domain extension.  It adds only `(S,J+1)` with the old
selected label's lower-tail vector and printed exponent increment. -/
theorem extendDomain_case1DisplayedRowStripNewLabel_updateData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hlevelLeast : leastValue s0 k0 = (level s0 k0 : ℤ))
    (hflat : FlatTailFromPred L S (t s0 k0) (level s0 k0 : ℤ))
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (hcol : J + 1 ≤ n (S + 1)) :
    IntroducedLabelExponentCertificates L n S (J + 1)
      (updateSelectedLabelVector S (J + 1) (lowerTailVector (t s0 k0) S (J : ℤ)) t)
      (updateSelectedLabelScalar S (J + 1)
        (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) := by
  exact hcert.extendDomain_case1DisplayedRowStripNewLabel_of_postData
    hfirst hlevelLeast hflat hS hSL hcol
    (Case1DisplayedRowStripExponentPostData.updateNewLabel t numerator leastValue)

/-- Level/tail invariant wrapper for the Case 1(2) displayed row-strip
new-label exponent-domain extension. -/
theorem extendDomain_case1DisplayedRowStripNewLabel_of_levelTailInvariants
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hfirst : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t)
    (hinv : IntroducedLabelLevelTailInvariants L n S J level t leastValue)
    (hS : 2 ≤ S) (hSL : S ≤ L)
    (hcol : J + 1 ≤ n (S + 1)) :
    IntroducedLabelExponentCertificates L n S (J + 1)
      (updateSelectedLabelVector S (J + 1) (lowerTailVector (t s0 k0) S (J : ℤ)) t)
      (updateSelectedLabelScalar S (J + 1)
        (numerator s0 k0 + (J1 : ℤ) * ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) :=
  hcert.extendDomain_case1DisplayedRowStripNewLabel_updateData hfirst
    (hinv.leastValue_eq_level hfirst.selectedIntroduced)
    (hinv.flatTail_abovePivot hfirst.selectedIntroduced hfirst.lt_selectedLevel)
    hS hSL hcol

end IntroducedLabelExponentCertificates

/-- Named recurrence data over the introduced labels at state `(S,J)`.

This packages the maps used to form the row-weight recurrence.  It does not
assert that these maps have been produced by Aoyagi's transition invariant. -/
structure IntroducedLabelRecurrenceState
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ) (α : Type*) where
  level : ℕ → ℕ → ℕ
  var : ℕ → ℕ → α

/-- Case 2 gap stated using integer least-value certificate data. -/
def case2IntroducedLabelLeastValueGap
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ) (leastValue : ℕ → ℕ → ℤ) : Prop :=
  ∀ {s k}, introducedLabel L n S J s k →
    ¬ ((J + 1 : ℤ) ≤ leastValue s k ∧ leastValue s k < (prefixMinNat n S : ℤ))

namespace IntroducedLabelRecurrenceState

/-- Case 2 gap for the Nat-valued recurrence levels of an introduced-label state. -/
def case2Gap {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) : Prop :=
  ∀ {s k}, introducedLabel L n S J s k →
    ¬ (J + 1 ≤ state.level s k ∧ state.level s k < prefixMinNat n S)

/-- The existing `leastValue = level` invariant converts an integer least-value
gap into the Nat-valued level gap required by the recurrence API. -/
theorem case2Gap_of_leastValueGap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α)
    {leastValue : ℕ → ℕ → ℤ}
    (hinv : IntroducedLabelLevelInvariants L n S J state.level leastValue)
    (hgap : case2IntroducedLabelLeastValueGap L n S J leastValue) :
    state.case2Gap := by
  intro s k hintro hlevel
  exact hgap hintro ⟨by
    rw [hinv.leastValue_eq_level hintro]
    exact_mod_cast hlevel.1, by
    rw [hinv.leastValue_eq_level hintro]
    exact_mod_cast hlevel.2⟩

/-- Case 2 successor recurrence state obtained by adding the new label
`(S,J+1)` at level `J` with selected variable `u`.

This is only a named post-data package; it does not assert that a blow-up chart
has produced the post-state. -/
def case2Succ {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α) :
    IntroducedLabelRecurrenceState L n S (J + 1) α where
  level s k := if s = S ∧ k = J + 1 then J else state.level s k
  var s k := if s = S ∧ k = J + 1 then u else state.var s k

@[simp] theorem case2Succ_level_new
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α) :
    (state.case2Succ u).level S (J + 1) = J := by
  simp [case2Succ]

@[simp] theorem case2Succ_var_new
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α) :
    (state.case2Succ u).var S (J + 1) = u := by
  simp [case2Succ]

theorem case2Succ_level_of_ne
    {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α)
    (hne : ¬ (s = S ∧ k = J + 1)) :
    (state.case2Succ u).level s k = state.level s k := by
  simp [case2Succ, hne]

theorem case2Succ_var_of_ne
    {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α)
    (hne : ¬ (s = S ∧ k = J + 1)) :
    (state.case2Succ u).var s k = state.var s k := by
  simp [case2Succ, hne]

/-- Candidate recurrence state obtained by relabelling old `(S,J+1)` data as
stage `(S+1,0)`.

The level and variable maps are copied verbatim.  This is only relabel
bookkeeping; the actual-width hypothesis is needed separately to prove that
the introduced-label finite products agree. -/
def stageRelabelSuccZero {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S (J + 1) α) :
    IntroducedLabelRecurrenceState L n (S + 1) 0 α where
  level := state.level
  var := state.var

@[simp] theorem stageRelabelSuccZero_level
    {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S (J + 1) α) :
    (state.stageRelabelSuccZero).level s k = state.level s k := rfl

@[simp] theorem stageRelabelSuccZero_var
    {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S (J + 1) α) :
    (state.stageRelabelSuccZero).var s k = state.var s k := rfl

/-- Supplied recurrence post-data for a Case 2 `J`-advance.

This records only agreement on old introduced labels and the assigned
level/variable of the new label `(S,J+1)`.  It does not assert that a blow-up
chart produces `post`. -/
structure Case2SuppliedPostData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (pre : IntroducedLabelRecurrenceState L n S J α)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (u : α) : Prop where
  level_old :
    ∀ {s k}, introducedLabel L n S J s k →
      post.level s k = pre.level s k
  var_old :
    ∀ {s k}, introducedLabel L n S J s k →
      post.var s k = pre.var s k
  level_new : post.level S (J + 1) = J
  var_new : post.var S (J + 1) = u

/-- The concrete `case2Succ` state supplies the recurrence post-data package.
This remains only recurrence data; no chart production is asserted. -/
theorem case2Succ_case2SuppliedPostData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α) :
    Case2SuppliedPostData state (state.case2Succ u) u where
  level_old := by
    intro s k hintro
    exact state.case2Succ_level_of_ne u (by
      rintro ⟨rfl, rfl⟩
      exact (not_introducedLabel_case2_new_before _ _ _ _) hintro)
  var_old := by
    intro s k hintro
    exact state.case2Succ_var_of_ne u (by
      rintro ⟨rfl, rfl⟩
      exact (not_introducedLabel_case2_new_before _ _ _ _) hintro)
  level_new := by simp
  var_new := by simp

/-- Adding the corrected Case 2 new label at level `J` preserves the Case 2 gap
for the successor state. -/
theorem case2Succ_case2Gap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α)
    (hgap : state.case2Gap) :
    (state.case2Succ u).case2Gap := by
  intro s k hintro hbad
  rcases introducedLabel_succ_cases hintro with hOld | hnew
  · have hne : ¬ (s = S ∧ k = J + 1) := by
      rintro ⟨rfl, rfl⟩
      rcases hOld.2 with hlt | ⟨_hs, hk⟩
      · omega
      · omega
    have hlevel := state.case2Succ_level_of_ne u hne
    have hbadOld : J + 1 ≤ state.level s k ∧ state.level s k < prefixMinNat n S := by
      constructor
      · rw [← hlevel]
        omega
      · rw [← hlevel]
        exact hbad.2
    exact hgap hOld hbadOld
  · rcases hnew with ⟨rfl, rfl⟩
    simpa using hbad.1

/-- Integer least-value form of the Case 2 successor gap.  Old labels keep
their least values, while the corrected new label has least value `J`. -/
theorem case2IntroducedLabelLeastValueGap_succ
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {leastValue leastValue' : ℕ → ℕ → ℤ}
    (hgap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    (hl_old :
      ∀ {s k}, introducedLabel L n S J s k → leastValue' s k = leastValue s k)
    (hl_new : leastValue' S (J + 1) = (J : ℤ)) :
    case2IntroducedLabelLeastValueGap L n S (J + 1) leastValue' := by
  intro s k hintro hbad
  rcases introducedLabel_succ_cases hintro with hOld | hnew
  · have hbadOld : (J + 1 : ℤ) ≤ leastValue s k ∧
        leastValue s k < (prefixMinNat n S : ℤ) := by
      constructor
      · have hle : (J + 1 : ℤ) ≤ leastValue' s k := by omega
        rw [hl_old hOld] at hle
        exact hle
      · have hlt := hbad.2
        rw [hl_old hOld] at hlt
        exact hlt
    exact hgap hOld hbadOld
  · rcases hnew with ⟨rfl, rfl⟩
    rw [hl_new] at hbad
    omega

/-- The equality bridge `leastValue = level` is preserved by the corrected Case
2 successor post-data. -/
theorem case2Succ_levelInvariants
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α)
    {leastValue leastValue' : ℕ → ℕ → ℤ}
    (hinv : IntroducedLabelLevelInvariants L n S J state.level leastValue)
    (hl_old :
      ∀ {s k}, introducedLabel L n S J s k → leastValue' s k = leastValue s k)
    (hl_new : leastValue' S (J + 1) = (J : ℤ)) :
    IntroducedLabelLevelInvariants L n S (J + 1)
      (state.case2Succ u).level leastValue' where
  leastValue_eq_level := by
    intro s k hintro
    rcases introducedLabel_succ_cases hintro with hOld | hnew
    · have hne : ¬ (s = S ∧ k = J + 1) := by
        rintro ⟨rfl, rfl⟩
        rcases hOld.2 with hlt | ⟨_hs, hk⟩
        · omega
        · omega
      rw [state.case2Succ_level_of_ne u hne, hl_old hOld, hinv.leastValue_eq_level hOld]
    · rcases hnew with ⟨rfl, rfl⟩
      rw [hl_new]
      simp

namespace Case2SuppliedPostData

/-- A supplied recurrence post-state and supplied corrected exponent post-data
preserve the equality bridge `leastValue = level` across a Case 2 `J`-advance.
This is invariant bookkeeping only; it does not assert chart production. -/
theorem levelInvariants_of_correctedExponentPostData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    {pre : IntroducedLabelRecurrenceState L n S J α}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) α}
    {u : α}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hpost : Case2SuppliedPostData pre post u)
    (hinv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (hexp :
      Case2CorrectedExponentPostData
        (L := L) (n := n) (S := S) (J := J)
        t t' numerator numerator' leastValue leastValue') :
    IntroducedLabelLevelInvariants L n S (J + 1) post.level leastValue' where
  leastValue_eq_level := by
    intro s k hintro
    rcases introducedLabel_succ_cases hintro with hOld | hnew
    · rw [hexp.leastValue_old hOld, hpost.level_old hOld,
        hinv.leastValue_eq_level hOld]
    · rcases hnew with ⟨rfl, rfl⟩
      rw [hexp.leastValue_new, hpost.level_new]

/-- Supplied recurrence post-data plus supplied corrected exponent post-data
convert an old integer least-value Case 2 gap into the successor recurrence
level gap. -/
theorem case2Gap_of_leastValueGap_of_correctedExponentPostData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    {pre : IntroducedLabelRecurrenceState L n S J α}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) α}
    {u : α}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hpost : Case2SuppliedPostData pre post u)
    (hinv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (hexp :
      Case2CorrectedExponentPostData
        (L := L) (n := n) (S := S) (J := J)
        t t' numerator numerator' leastValue leastValue')
    (hgap : case2IntroducedLabelLeastValueGap L n S J leastValue) :
    post.case2Gap :=
  case2Gap_of_leastValueGap post
    (hpost.levelInvariants_of_correctedExponentPostData hinv hexp)
    (case2IntroducedLabelLeastValueGap_succ hgap
      hexp.leastValue_old hexp.leastValue_new)

end Case2SuppliedPostData

/-- Least-value successor data can also feed the recurrence-state Case 2 gap
through the equality bridge. -/
theorem case2Succ_case2Gap_of_leastValueGap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (u : α)
    {leastValue leastValue' : ℕ → ℕ → ℤ}
    (hinv : IntroducedLabelLevelInvariants L n S J state.level leastValue)
    (hgap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    (hl_old :
      ∀ {s k}, introducedLabel L n S J s k → leastValue' s k = leastValue s k)
    (hl_new : leastValue' S (J + 1) = (J : ℤ)) :
    (state.case2Succ u).case2Gap :=
  case2Gap_of_leastValueGap (state.case2Succ u)
    (state.case2Succ_levelInvariants u hinv hl_old hl_new)
    (case2IntroducedLabelLeastValueGap_succ hgap hl_old hl_new)

/-- Case 1(1) same-domain recurrence state obtained by lowering the selected
old label's level to the current pivot level `J`.

Only the recurrence level assigned to `(s0,k0)` changes.  The recurrence-label
variables are left unchanged; this is not a statement about raw residual matrix
coordinates, whose row strip is separately rescaled in the selected-old chart.
-/
def case1SelectedOldLevelMove {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) (s0 k0 : ℕ) :
    IntroducedLabelRecurrenceState L n S J α where
  level s k := if (s, k) = (s0, k0) then J else state.level s k
  var s k := state.var s k

@[simp] theorem case1SelectedOldLevelMove_level_selected
    {L : ℕ} {n : ℕ → ℕ} {S J s0 k0 : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) :
    (state.case1SelectedOldLevelMove s0 k0).level s0 k0 = J := by
  simp [case1SelectedOldLevelMove]

theorem case1SelectedOldLevelMove_level_of_ne
    {L : ℕ} {n : ℕ → ℕ} {S J s0 k0 s k : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (hne : (s, k) ≠ (s0, k0)) :
    (state.case1SelectedOldLevelMove s0 k0).level s k = state.level s k := by
  change (if (s, k) = (s0, k0) then J else state.level s k) = state.level s k
  simp [hne]

@[simp] theorem case1SelectedOldLevelMove_var
    {L : ℕ} {n : ℕ → ℕ} {S J s0 k0 s k : ℕ} {α : Type*}
    (state : IntroducedLabelRecurrenceState L n S J α) :
    (state.case1SelectedOldLevelMove s0 k0).var s k = state.var s k := rfl

/-- Supplied recurrence post-data for Case 1(1)'s selected-old level move.

The selected old label is already in the `(S,J)` introduced-label domain.  The
`pre` state has that label at level `J+J1`; the `post` state has the same
selected recurrence-label variable at level `J`; all other introduced labels
keep their level and recurrence-label variable data.  This is recurrence
bookkeeping for the source's Case 1(1) assignment of `b'_i`; it does not
construct a chart or make a claim about raw residual matrix coordinates. -/
structure Case1SelectedOldLevelMoveData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 : ℕ} {α : Type*}
    (pre post : IntroducedLabelRecurrenceState L n S J α)
    (s0 k0 : ℕ) (u : α) : Prop where
  selectedIntroduced : introducedLabel L n S J s0 k0
  pre_level_selected : pre.level s0 k0 = J + J1
  post_level_selected : post.level s0 k0 = J
  pre_var_selected : pre.var s0 k0 = u
  post_var_selected : post.var s0 k0 = u
  level_old :
    ∀ {s k}, introducedLabel L n S J s k → (s, k) ≠ (s0, k0) →
      post.level s k = pre.level s k
  var_old :
    ∀ {s k}, introducedLabel L n S J s k → (s, k) ≠ (s0, k0) →
      post.var s k = pre.var s k

/-- The concrete same-domain Case 1(1) level override supplies the abstract
moved-level recurrence data. -/
theorem case1SelectedOldLevelMove_levelMoveData
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ} {α : Type*}
    (pre : IntroducedLabelRecurrenceState L n S J α)
    (hsel : introducedLabel L n S J s0 k0)
    (hlevel : pre.level s0 k0 = J + J1) :
    Case1SelectedOldLevelMoveData (J1 := J1)
      pre (pre.case1SelectedOldLevelMove s0 k0) s0 k0 (pre.var s0 k0) where
  selectedIntroduced := hsel
  pre_level_selected := hlevel
  post_level_selected := by simp
  pre_var_selected := rfl
  post_var_selected := by simp
  level_old := by
    intro s k _hintro hne
    exact pre.case1SelectedOldLevelMove_level_of_ne hne
  var_old := by
    intro s k _hintro _hne
    simp

end IntroducedLabelRecurrenceState

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

/-- If all factors in a recurrence tail are `1`, the tail product is `1`. -/
theorem monomialTail_eq_one_of_forall_eq_one
    (step : ℕ → α) (a k : ℕ)
    (hstep : ∀ r, r < k → step (a + r) = 1) :
    monomialTail step a k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [monomialTail_succ, hstep k (Nat.lt_succ_self k)]
      rw [ih (fun r hr ↦ hstep r (Nat.lt_trans hr (Nat.lt_succ_self k)))]
      simp

/-- A recurrence is constant across an interval whose step factors are all `1`. -/
theorem monomialRec_eq_of_step_eq_one_on_Ico
    (step : ℕ → α) {a b : ℕ} (hle : a ≤ b)
    (hstep : ∀ k, a ≤ k → k < b → step k = 1) :
    monomialRec step b = monomialRec step a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [monomialRec_add_eq_tail_mul]
  rw [monomialTail_eq_one_of_forall_eq_one step a d]
  · simp
  · intro r hr
    exact hstep (a + r) (by omega) (by omega)

/-- Two monomial recurrences agree up to level `i` if their step factors agree
strictly before `i`. -/
theorem monomialRec_eq_of_step_eq_on_lt
    (step step' : ℕ → α) {i : ℕ}
    (hstep : ∀ r, r < i → step' r = step r) :
    monomialRec step' i = monomialRec step i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [monomialRec_succ, monomialRec_succ, hstep i (Nat.lt_succ_self i)]
      rw [ih (fun r hr ↦ hstep r (Nat.lt_trans hr (Nat.lt_succ_self i)))]

/-- If one recurrence step at level `J` gains a factor `u` and all other steps
are unchanged, then all later recurrence weights gain the same factor. -/
theorem monomialRec_eq_mul_of_step_eq_mul_at
    (step step' : ℕ → α) (u : α) (J : ℕ)
    (hstepJ : step' J = u * step J)
    (hstep_ne : ∀ r, r ≠ J → step' r = step r) :
    ∀ i, J + 1 ≤ i → monomialRec step' i = u * monomialRec step i := by
  intro i hi
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero =>
      calc
        monomialRec step' (J + 1)
            = step' J * monomialRec step' J := rfl
        _ = (u * step J) * monomialRec step J := by
              rw [hstepJ]
              rw [monomialRec_eq_of_step_eq_on_lt step step'
                (fun r hr ↦ hstep_ne r (by omega))]
        _ = u * monomialRec step (J + 1) := by
              rw [monomialRec_succ]
              ac_rfl
  | succ d ih =>
      rw [Nat.add_succ, monomialRec_succ, ih (by omega)]
      rw [hstep_ne (J + 1 + d) (by omega), monomialRec_succ]
      ac_rfl

/-- Modify one recurrence factor by multiplying the step at level `J` by `u`.
With Aoyagi's convention, this affects row weights starting at row `J+1`. -/
def mulStepAt (step : ℕ → α) (u : α) (J r : ℕ) : α :=
  if r = J then u * step r else step r

@[simp] theorem mulStepAt_self (step : ℕ → α) (u : α) (J : ℕ) :
    mulStepAt step u J J = u * step J := by
  simp [mulStepAt]

theorem mulStepAt_of_ne (step : ℕ → α) (u : α) {J r : ℕ} (hne : r ≠ J) :
    mulStepAt step u J r = step r := by
  simp [mulStepAt, hne]

/-- A single factor inserted at level `J` does not affect row weights up to
row `J`. -/
theorem monomialRec_mulStepAt_eq_of_le
    (step : ℕ → α) (u : α) {J i : ℕ} (hi : i ≤ J) :
    monomialRec (mulStepAt step u J) i = monomialRec step i :=
  monomialRec_eq_of_step_eq_on_lt step (mulStepAt step u J)
    (fun r hr ↦ mulStepAt_of_ne step u (by omega : r ≠ J))

/-- A single factor inserted at level `J` multiplies every row weight from
row `J+1` onward. -/
theorem monomialRec_mulStepAt_eq_mul_of_ge
    (step : ℕ → α) (u : α) {J i : ℕ} (hi : J + 1 ≤ i) :
    monomialRec (mulStepAt step u J) i = u * monomialRec step i :=
  monomialRec_eq_mul_of_step_eq_mul_at step (mulStepAt step u J) u J
    (mulStepAt_self step u J)
    (fun r hne ↦ mulStepAt_of_ne step u (r := r) hne) i hi

/-- Case 1(2) recurrence split on strip rows.  If the old selected factor is
at level `h` and the new factor is at level `J`, then rows `J+1..h` see the
new post factor but not the old source factor. -/
theorem monomialRec_mulStepAt_case1_strip_split
    (step : ℕ → α) (u : α) {J h i : ℕ}
    (hJ : J + 1 ≤ i) (hih : i ≤ h) :
    monomialRec (mulStepAt step u h) i = monomialRec step i ∧
      monomialRec (mulStepAt step u J) i = u * monomialRec step i :=
  ⟨monomialRec_mulStepAt_eq_of_le step u hih,
    monomialRec_mulStepAt_eq_mul_of_ge step u hJ⟩

/-- Below the Case 1(2) strip, moving the same single factor from the old
selected level `h` down to level `J` gives the same row weight: both are
`u` times the factored-base recurrence weight. -/
theorem monomialRec_mulStepAt_case1_lower_eq
    (step : ℕ → α) (u : α) {J h i : ℕ}
    (hJh : J < h) (hih : h + 1 ≤ i) :
    monomialRec (mulStepAt step u h) i =
      monomialRec (mulStepAt step u J) i := by
  rw [monomialRec_mulStepAt_eq_mul_of_ge step u hih]
  rw [monomialRec_mulStepAt_eq_mul_of_ge step u (by omega : J + 1 ≤ i)]

/-- Case 1(1) selected-old level lowering as a pure recurrence calculation.

If the selected old factor is moved from level `J+J1` down to level `J`, then
on active residual rows `i >= J+1` the lowered recurrence is obtained from the
old recurrence by multiplying exactly the strip rows `i <= J+J1` by the
selected old factor.  The recurrence `step` is a supplied base recurrence with
the selected factor kept separate. -/
theorem monomialRec_mulStepAt_case1_selectedOld_postWeight
    (step : ℕ → α) (u : α) {J J1 i : ℕ} (hi : J + 1 ≤ i) :
    (if i ≤ J + J1 then
        u * monomialRec (mulStepAt step u (J + J1)) i
      else
        monomialRec (mulStepAt step u (J + J1)) i) =
      monomialRec (mulStepAt step u J) i := by
  by_cases hstrip : i ≤ J + J1
  · rw [if_pos hstrip]
    rw [monomialRec_mulStepAt_eq_of_le step u hstrip]
    rw [monomialRec_mulStepAt_eq_mul_of_ge step u hi]
  · have hbelow : J + J1 + 1 ≤ i := by omega
    rw [if_neg hstrip]
    rw [monomialRec_mulStepAt_eq_mul_of_ge step u hbelow]
    rw [monomialRec_mulStepAt_eq_mul_of_ge step u hi]

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

/-- Recurrence factor obtained as the product of variables at a given level. -/
def levelProductStep {β : Type*} (labels : Finset β)
    (level : β → ℕ) (var : β → α) (r : ℕ) : α :=
  (labels.filter (fun p ↦ level p = r)).prod var

/-- Inserting a new label at the queried level multiplies that recurrence factor
by the new variable, provided old labels keep their level and variable data. -/
theorem levelProductStep_insert_eq_mul_of_new
    {β : Type*} [DecidableEq β] (labels : Finset β) {a : β}
    (ha : a ∉ labels) (level level' : β → ℕ) (var var' : β → α)
    (r : ℕ) (u : α)
    (hlevel_a : level' a = r) (hvar_a : var' a = u)
    (hlevel_old : ∀ p, p ∈ labels → level' p = level p)
    (hvar_old : ∀ p, p ∈ labels → var' p = var p) :
    levelProductStep (insert a labels) level' var' r =
      u * levelProductStep labels level var r := by
  have hfilter_old :
      labels.filter (fun p ↦ level' p = r) =
        labels.filter (fun p ↦ level p = r) := by
    ext p
    by_cases hp : p ∈ labels
    · simp [hp, hlevel_old p hp]
    · simp [hp]
  have ha_filter : a ∉ labels.filter (fun p ↦ level' p = r) := by
    intro hp
    exact ha ((Finset.mem_filter.mp hp).1)
  calc
    levelProductStep (insert a labels) level' var' r
        = (insert a (labels.filter (fun p ↦ level' p = r))).prod var' := by
          rw [levelProductStep, Finset.filter_insert]
          simp [hlevel_a]
    _ = u * (labels.filter (fun p ↦ level' p = r)).prod var' := by
          rw [Finset.prod_insert ha_filter, hvar_a]
    _ = u * (labels.filter (fun p ↦ level p = r)).prod var' := by
          rw [hfilter_old]
    _ = u * (labels.filter (fun p ↦ level p = r)).prod var := by
          congr 1
          apply Finset.prod_congr rfl
          intro p hp
          exact hvar_old p ((Finset.mem_filter.mp hp).1)

/-- Inserting a new label at a different level leaves the queried recurrence
factor unchanged, provided old labels keep their level and variable data. -/
theorem levelProductStep_insert_eq_of_ne
    {β : Type*} [DecidableEq β] (labels : Finset β) {a : β}
    (level level' : β → ℕ) (var var' : β → α)
    {r newLevel : ℕ}
    (hlevel_a : level' a = newLevel) (hne : r ≠ newLevel)
    (hlevel_old : ∀ p, p ∈ labels → level' p = level p)
    (hvar_old : ∀ p, p ∈ labels → var' p = var p) :
    levelProductStep (insert a labels) level' var' r =
      levelProductStep labels level var r := by
  have ha_ne : level' a ≠ r := by
    rw [hlevel_a]
    exact fun h ↦ hne h.symm
  have hfilter_old :
      labels.filter (fun p ↦ level' p = r) =
        labels.filter (fun p ↦ level p = r) := by
    ext p
    by_cases hp : p ∈ labels
    · simp [hp, hlevel_old p hp]
    · simp [hp]
  calc
    levelProductStep (insert a labels) level' var' r
        = (labels.filter (fun p ↦ level' p = r)).prod var' := by
          rw [levelProductStep, Finset.filter_insert]
          simp [ha_ne]
    _ = (labels.filter (fun p ↦ level p = r)).prod var' := by
          rw [hfilter_old]
    _ = (labels.filter (fun p ↦ level p = r)).prod var := by
          apply Finset.prod_congr rfl
          intro p hp
          exact hvar_old p ((Finset.mem_filter.mp hp).1)

/-- Scaling the variable of one existing label scales the recurrence factor at
that label's level. -/
theorem levelProductStep_updateVar_eq_mul_of_mem
    {β : Type*} (labels : Finset β) {a : β}
    (ha : a ∈ labels) (level : β → ℕ) (var var' : β → α) (u : α)
    (hvar_a : var' a = u * var a)
    (hvar_old : ∀ p, p ∈ labels → p ≠ a → var' p = var p) :
    levelProductStep labels level var' (level a) =
      u * levelProductStep labels level var (level a) := by
  classical
  let filtered := labels.filter (fun p ↦ level p = level a)
  have ha_filter : a ∈ filtered := by
    simp [filtered, ha]
  have hnot : a ∉ filtered.erase a := by simp
  calc
    levelProductStep labels level var' (level a)
        = filtered.prod var' := rfl
    _ = (insert a (filtered.erase a)).prod var' := by
          rw [Finset.insert_erase ha_filter]
    _ = var' a * (filtered.erase a).prod var' := by
          rw [Finset.prod_insert hnot]
    _ = (u * var a) * (filtered.erase a).prod var := by
          rw [hvar_a]
          congr 1
          apply Finset.prod_congr rfl
          intro p hp
          have hp' := Finset.mem_erase.mp hp
          exact hvar_old p ((Finset.mem_filter.mp hp'.2).1) hp'.1
    _ = u * (var a * (filtered.erase a).prod var) := by
          ac_rfl
    _ = u * (insert a (filtered.erase a)).prod var := by
          rw [Finset.prod_insert hnot]
    _ = u * levelProductStep labels level var (level a) := by
          rw [Finset.insert_erase ha_filter]
          rfl

/-- Scaling the variable of one existing label leaves all other recurrence
factors unchanged. -/
theorem levelProductStep_updateVar_eq_of_ne
    {β : Type*} (labels : Finset β) {a : β}
    (level : β → ℕ) (var var' : β → α) {r : ℕ}
    (hne : r ≠ level a)
    (hvar_old : ∀ p, p ∈ labels → p ≠ a → var' p = var p) :
    levelProductStep labels level var' r =
      levelProductStep labels level var r := by
  classical
  apply Finset.prod_congr rfl
  intro p hp
  exact hvar_old p ((Finset.mem_filter.mp hp).1) (by
    intro hpa
    subst hpa
    exact hne (Finset.mem_filter.mp hp).2.symm)

/-- A same-domain selected-variable scaling changes the recurrence factor
function by inserting one multiplicative factor at the selected label's level.
-/
theorem levelProductStep_eq_mulStepAt_of_updateSelected
    {β : Type*} (labels : Finset β) {a : β}
    (ha : a ∈ labels) (level : β → ℕ) (var var' : β → α) (u : α)
    (hvar_a : var' a = u * var a)
    (hvar_old : ∀ p, p ∈ labels → p ≠ a → var' p = var p) :
    levelProductStep labels level var' =
      mulStepAt (levelProductStep labels level var) u (level a) := by
  classical
  funext r
  by_cases hr : r = level a
  · subst r
    simp [mulStepAt, levelProductStep_updateVar_eq_mul_of_mem
      labels ha level var var' u hvar_a hvar_old]
  · rw [mulStepAt_of_ne (levelProductStep labels level var) u hr]
    exact levelProductStep_updateVar_eq_of_ne labels level var var' hr hvar_old

/-- Removing one selected label gives a base recurrence whose reinsertion is
exactly `mulStepAt` at the selected label's level. -/
theorem levelProductStep_eq_mulStepAt_erase
    {β : Type*} [DecidableEq β] (labels : Finset β) {a : β}
    (ha : a ∈ labels) (level : β → ℕ) (var : β → α) :
    levelProductStep labels level var =
      mulStepAt (levelProductStep (labels.erase a) level var)
        (var a) (level a) := by
  classical
  funext r
  by_cases hr : r = level a
  · subst r
    rw [mulStepAt_self]
    calc
      levelProductStep labels level var (level a)
          = levelProductStep (insert a (labels.erase a)) level var
              (level a) := by rw [Finset.insert_erase ha]
      _ = var a * levelProductStep (labels.erase a) level var
              (level a) :=
            levelProductStep_insert_eq_mul_of_new
              (labels.erase a)
              (a := a)
              (by simp)
              level level var var (level a) (var a) rfl rfl
              (fun p _ ↦ rfl)
              (fun p _ ↦ rfl)
  · rw [← Finset.insert_erase ha]
    rw [mulStepAt_of_ne
      (levelProductStep ((insert a (labels.erase a)).erase a) level var)
      (var a) hr]
    simpa using
      levelProductStep_insert_eq_of_ne
        (labels.erase a)
        (a := a)
        level level var var rfl hr
        (fun p _ ↦ rfl)
        (fun p _ ↦ rfl)

/-- If two level/variable assignments agree away from one erased label, their
erased finite-product recurrence factors agree. -/
theorem levelProductStep_erase_eq_of_eq_on_erase
    {β : Type*} [DecidableEq β] (labels : Finset β) {a : β}
    (level level' : β → ℕ) (var var' : β → α)
    (hlevel_old : ∀ p, p ∈ labels → p ≠ a → level' p = level p)
    (hvar_old : ∀ p, p ∈ labels → p ≠ a → var' p = var p) :
    levelProductStep (labels.erase a) level' var' =
      levelProductStep (labels.erase a) level var := by
  classical
  funext r
  unfold levelProductStep
  have hfilter :
      (labels.erase a).filter (fun p ↦ level' p = r) =
        (labels.erase a).filter (fun p ↦ level p = r) := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_filter]
      exact ⟨hp.1, by
        rw [← hlevel_old p (Finset.mem_of_mem_erase hp.1)
          (Finset.ne_of_mem_erase hp.1)]
        exact hp.2⟩
    · intro hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_filter]
      exact ⟨hp.1, by
        rw [hlevel_old p (Finset.mem_of_mem_erase hp.1)
          (Finset.ne_of_mem_erase hp.1)]
        exact hp.2⟩
  rw [hfilter]
  apply Finset.prod_congr rfl
  intro p hp
  exact hvar_old p
    (Finset.mem_of_mem_erase (Finset.mem_filter.mp hp).1)
    (Finset.ne_of_mem_erase (Finset.mem_filter.mp hp).1)

namespace IntroducedLabelRecurrenceState

/-- The recurrence factor obtained from the introduced labels of a packaged state. -/
def step {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α) (r : ℕ) : α :=
  levelProductStep (introducedLabelFinset L n S J)
    (fun p : Σ _ : ℕ, ℕ ↦ state.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state.var p.1 p.2) r

/-- The base recurrence obtained by erasing one selected introduced label from
the finite product defining `step`. -/
def erasedStep {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (s0 k0 : ℕ) (r : ℕ) : α :=
  levelProductStep ((introducedLabelFinset L n S J).erase (Sigma.mk s0 k0))
    (fun p : Σ _ : ℕ, ℕ ↦ state.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state.var p.1 p.2) r

/-- Reinsert an erased selected label to recover the packaged recurrence
factor as a single `mulStepAt`. -/
theorem step_eq_mulStepAt_erasedStep
    {L : ℕ} {n : ℕ → ℕ} {S J s0 k0 : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (hsel : introducedLabel L n S J s0 k0) :
    state.step =
      mulStepAt (state.erasedStep s0 k0)
        (state.var s0 k0) (state.level s0 k0) := by
  exact levelProductStep_eq_mulStepAt_erase
    (introducedLabelFinset L n S J)
    (a := Sigma.mk s0 k0)
    ((mem_introducedLabelFinset).mpr hsel)
    (fun p : Σ _ : ℕ, ℕ ↦ state.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state.var p.1 p.2)

/-- Row weights generated by the introduced-label recurrence of a packaged state. -/
def weight {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α) (i : ℕ) : α :=
  monomialRec state.step i

/-- Under actual-width exhaustion, the stage-relabelled recurrence factors are
the old post-state recurrence factors. -/
theorem stageRelabelSuccZero_step_eq
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (hwidth : n (S + 1) = J + 1) :
    (state.stageRelabelSuccZero).step = state.step := by
  funext r
  simp [step, stageRelabelSuccZero,
    ← introducedLabelFinset_currentSucc_eq_succStage_zero_of_nextWidth_eq
      L n hwidth]

/-- Under actual-width exhaustion, the stage-relabelled recurrence weights are
the old post-state weights. -/
theorem stageRelabelSuccZero_weight_eq
    {L : ℕ} {n : ℕ → ℕ} {S J i : ℕ}
    (state : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (hwidth : n (S + 1) = J + 1) :
    (state.stageRelabelSuccZero).weight i = state.weight i := by
  simp [weight, stageRelabelSuccZero_step_eq state hwidth]

/-- The packaged recurrence weight attached to a displayed Case 2 residual row. -/
def case2ResidualRowWeight {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (i : Case2ResidualRowIndex n S J) : α :=
  state.weight (case2ResidualRowLevel n S J i)

/-- Supplied same-domain source substitution data for the old selected Case 1
exceptional variable.

The `source` state represents the original recurrence after the source
substitution `old = u * old'`, not the raw pre-chart coordinate recurrence.
It has the same levels as `factoredBase`, agrees with `factoredBase` on all
introduced variables except `(s0,k0)`, and has selected variable
`source.var s0 k0 = u * factoredBase.var s0 k0`.

This is recurrence bookkeeping only; it does not construct the selected-old
chart or prove source validity beyond the supplied introduced-label
hypothesis. -/
structure Case1SelectedOldFactoredBaseData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (source factoredBase : IntroducedLabelRecurrenceState L n S J α)
    (s0 k0 : ℕ) (u : α) : Prop where
  selectedIntroduced : introducedLabel L n S J s0 k0
  level_eq : source.level = factoredBase.level
  var_selected : source.var s0 k0 = u * factoredBase.var s0 k0
  var_old :
    ∀ {s k}, introducedLabel L n S J s k → (s, k) ≠ (s0, k0) →
      source.var s k = factoredBase.var s k

namespace Case1SelectedOldFactoredBaseData

/-- At the selected old label's level, the substituted source recurrence factor
is the factored-base recurrence factor multiplied by the selected chart
variable. -/
theorem step_selectedLevel_eq_mul
    {L : ℕ} {n : ℕ → ℕ} {S J s0 k0 : ℕ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J α}
    {u : α}
    (data : Case1SelectedOldFactoredBaseData source factoredBase s0 k0 u) :
    source.step (factoredBase.level s0 k0) =
      u * factoredBase.step (factoredBase.level s0 k0) := by
  rw [step, step, data.level_eq]
  exact levelProductStep_updateVar_eq_mul_of_mem
    (introducedLabelFinset L n S J)
    (a := Sigma.mk s0 k0)
    ((mem_introducedLabelFinset).mpr data.selectedIntroduced)
    (fun p : Σ _ : ℕ, ℕ ↦ factoredBase.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ factoredBase.var p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ source.var p.1 p.2)
    u data.var_selected
    (fun p hp hpne ↦ by
      exact data.var_old (mem_introducedLabelFinset.mp hp) (by
        intro hpair
        apply hpne
        cases p with
        | mk s k =>
            cases hpair
            rfl))

/-- Away from the selected old label's level, the substituted source and
factored-base recurrence factors agree. -/
theorem step_eq_of_ne_selectedLevel
    {L : ℕ} {n : ℕ → ℕ} {S J s0 k0 r : ℕ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J α}
    {u : α}
    (data : Case1SelectedOldFactoredBaseData source factoredBase s0 k0 u)
    (hne : r ≠ factoredBase.level s0 k0) :
    source.step r = factoredBase.step r := by
  rw [step, step, data.level_eq]
  exact levelProductStep_updateVar_eq_of_ne
    (a := Sigma.mk s0 k0)
    (introducedLabelFinset L n S J)
    (fun p : Σ _ : ℕ, ℕ ↦ factoredBase.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ factoredBase.var p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ source.var p.1 p.2)
    hne
    (fun p hp hpne ↦ by
      exact data.var_old (mem_introducedLabelFinset.mp hp) (by
        intro hpair
        apply hpne
        cases p with
        | mk s k =>
            cases hpair
            rfl))

/-- The substituted source recurrence factors are exactly the factored-base
recurrence with a single factor `u` inserted at the selected old label's
level. -/
theorem step_eq_mulStepAt_selectedLevel
    {L : ℕ} {n : ℕ → ℕ} {S J s0 k0 : ℕ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J α}
    {u : α}
    (data : Case1SelectedOldFactoredBaseData source factoredBase s0 k0 u) :
    source.step = mulStepAt factoredBase.step u (factoredBase.level s0 k0) := by
  funext r
  by_cases hr : r = factoredBase.level s0 k0
  · subst r
    simp [mulStepAt, data.step_selectedLevel_eq_mul]
  · rw [mulStepAt_of_ne factoredBase.step u hr]
    exact data.step_eq_of_ne_selectedLevel hr

/-- First-jump specialization: if the selected old label has Case 1 level
`J+J1`, the substituted source recurrence is the factored-base recurrence with
a single factor inserted at level `J+J1`. -/
theorem step_eq_mulStepAt_of_firstJump
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J α}
    {u : α} {vector : ℕ → ℕ → ℕ → ℤ}
    (data : Case1SelectedOldFactoredBaseData source factoredBase s0 k0 u)
    (hfirst :
      Case1FirstJumpHypotheses L n S J J1 s0 k0 factoredBase.level vector) :
    source.step = mulStepAt factoredBase.step u (J + J1) := by
  rw [data.step_eq_mulStepAt_selectedLevel, hfirst.selectedLevel]

end Case1SelectedOldFactoredBaseData

namespace Case1SelectedOldLevelMoveData

/-- The erased base recurrence is unchanged by the selected-old level move. -/
theorem post_erasedStep_eq_pre_erasedStep
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {pre post : IntroducedLabelRecurrenceState L n S J α}
    {u : α}
    (data :
      Case1SelectedOldLevelMoveData (J1 := J1) pre post s0 k0 u) :
    post.erasedStep s0 k0 = pre.erasedStep s0 k0 := by
  exact levelProductStep_erase_eq_of_eq_on_erase
    (introducedLabelFinset L n S J)
    (a := Sigma.mk s0 k0)
    (fun p : Σ _ : ℕ, ℕ ↦ pre.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ post.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ pre.var p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ post.var p.1 p.2)
    (fun p hp hpne ↦ by
      exact data.level_old (mem_introducedLabelFinset.mp hp) (by
        intro hpair
        apply hpne
        cases p with
        | mk s k =>
            cases hpair
            rfl))
    (fun p hp hpne ↦ by
      exact data.var_old (mem_introducedLabelFinset.mp hp) (by
        intro hpair
        apply hpne
        cases p with
        | mk s k =>
            cases hpair
            rfl))

/-- The pre-state recurrence is the erased base recurrence with the selected
old factor reinserted at level `J+J1`. -/
theorem pre_step_eq_mulStepAt
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {pre post : IntroducedLabelRecurrenceState L n S J α}
    {u : α}
    (data :
      Case1SelectedOldLevelMoveData (J1 := J1) pre post s0 k0 u) :
    pre.step = mulStepAt (pre.erasedStep s0 k0) u (J + J1) := by
  rw [pre.step_eq_mulStepAt_erasedStep data.selectedIntroduced,
    data.pre_var_selected, data.pre_level_selected]

/-- The post-state recurrence is the same erased base recurrence with the
selected old factor reinserted at level `J`. -/
theorem post_step_eq_mulStepAt
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {pre post : IntroducedLabelRecurrenceState L n S J α}
    {u : α}
    (data :
      Case1SelectedOldLevelMoveData (J1 := J1) pre post s0 k0 u) :
    post.step = mulStepAt (pre.erasedStep s0 k0) u J := by
  rw [post.step_eq_mulStepAt_erasedStep data.selectedIntroduced,
    data.post_erasedStep_eq_pre_erasedStep (J1 := J1), data.post_var_selected,
    data.post_level_selected]

end Case1SelectedOldLevelMoveData

/-- If a supplied Case 2 successor state keeps all old introduced-label data and
adds `(S,J+1)` at level `J` with variable `u`, then the recurrence factor at
level `J` gains exactly that factor. -/
theorem step_succ_current_eq_new_mul
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : actualWidthLabel L n S (J + 1))
    (state : IntroducedLabelRecurrenceState L n S J α)
    (state' : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (u : α)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.level s k = state.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.var s k = state.var s k)
    (hlevel_new : state'.level S (J + 1) = J)
    (hvar_new : state'.var S (J + 1) = u) :
    state'.step J = u * state.step J := by
  rw [step, step, introducedLabelFinset_succ_eq_insert hnew]
  exact levelProductStep_insert_eq_mul_of_new
    (introducedLabelFinset L n S J)
    (a := Sigma.mk S (J + 1))
    (not_mem_introducedLabelFinset_case2_new_before L n S J)
    (fun p : Σ _ : ℕ, ℕ ↦ state.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state'.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state.var p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state'.var p.1 p.2)
    J u hlevel_new hvar_new
    (fun p hp ↦ hlevel_old (mem_introducedLabelFinset.mp hp))
    (fun p hp ↦ hvar_old (mem_introducedLabelFinset.mp hp))

/-- Under the same supplied Case 2 successor post-data, recurrence factors away
from level `J` are unchanged. -/
theorem step_succ_current_eq_of_ne
    {L : ℕ} {n : ℕ → ℕ} {S J r : ℕ}
    (hnew : actualWidthLabel L n S (J + 1))
    (state : IntroducedLabelRecurrenceState L n S J α)
    (state' : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.level s k = state.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.var s k = state.var s k)
    (hlevel_new : state'.level S (J + 1) = J)
    (hne : r ≠ J) :
    state'.step r = state.step r := by
  rw [step, step, introducedLabelFinset_succ_eq_insert hnew]
  exact levelProductStep_insert_eq_of_ne
    (introducedLabelFinset L n S J)
    (a := Sigma.mk S (J + 1))
    (fun p : Σ _ : ℕ, ℕ ↦ state.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state'.level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state.var p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ state'.var p.1 p.2)
    hlevel_new hne
    (fun p hp ↦ hlevel_old (mem_introducedLabelFinset.mp hp))
    (fun p hp ↦ hvar_old (mem_introducedLabelFinset.mp hp))

/-- A supplied Case 2 successor state agrees with the old recurrence weights
up to the pivot level. -/
theorem weight_succ_current_eq_of_le
    {L : ℕ} {n : ℕ → ℕ} {S J i : ℕ}
    (hnew : actualWidthLabel L n S (J + 1))
    (state : IntroducedLabelRecurrenceState L n S J α)
    (state' : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.level s k = state.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.var s k = state.var s k)
    (hlevel_new : state'.level S (J + 1) = J)
    (hi : i ≤ J) :
    state'.weight i = state.weight i := by
  exact monomialRec_eq_of_step_eq_on_lt state.step state'.step
    (fun r hr ↦ state.step_succ_current_eq_of_ne hnew state' hlevel_old hvar_old
      hlevel_new (by omega))

/-- A supplied Case 2 successor state has Aoyagi's displayed row-weight update:
from row `J+1` onward, every recurrence weight is multiplied by the new selected
variable. -/
theorem weight_succ_current_eq_new_mul_of_ge
    {L : ℕ} {n : ℕ → ℕ} {S J i : ℕ}
    (hnew : actualWidthLabel L n S (J + 1))
    (state : IntroducedLabelRecurrenceState L n S J α)
    (state' : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (u : α)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.level s k = state.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.var s k = state.var s k)
    (hlevel_new : state'.level S (J + 1) = J)
    (hvar_new : state'.var S (J + 1) = u)
    (hi : J + 1 ≤ i) :
    state'.weight i = u * state.weight i :=
  monomialRec_eq_mul_of_step_eq_mul_at state.step state'.step u J
    (state.step_succ_current_eq_new_mul hnew state' u hlevel_old hvar_old
      hlevel_new hvar_new)
    (fun r hr ↦ state.step_succ_current_eq_of_ne (r := r) hnew state'
      hlevel_old hvar_old hlevel_new hr)
    i hi

end IntroducedLabelRecurrenceState

/-- Source-facing Case 2 recurrence-weight update: if a supplied post-state
keeps old introduced-label recurrence data and assigns the corrected new label
`(S,J+1)` to level `J` with variable `u`, then Aoyagi's displayed
`b'_i = u*b_i` recurrence update holds for every row from `J+1` onward.

This is conditional recurrence bookkeeping; it does not prove that a blow-up
chart produces the post-state. -/
theorem CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (state : IntroducedLabelRecurrenceState L n S J α)
    (state' : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (u : α)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.level s k = state.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.var s k = state.var s k)
    (hlevel_new : state'.level S (J + 1) = J)
    (hvar_new : state'.var S (J + 1) = u) :
    ∀ i, J + 1 ≤ i → state'.weight i = u * state.weight i :=
  fun i hi ↦ state.weight_succ_current_eq_new_mul_of_ge hnew.introduced.1
    (i := i) state' u hlevel_old hvar_old hlevel_new hvar_new hi

namespace IntroducedLabelRecurrenceState.Case2SuppliedPostData

/-- A supplied Case 2 post-data package gives Aoyagi's recurrence update from
row `J+1` onward, under the actual source-validity of the new label. -/
theorem weight_succ_current_eq_new_mul_of_ge
    {L : ℕ} {n : ℕ → ℕ} {S J i : ℕ}
    {pre : IntroducedLabelRecurrenceState L n S J α}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) α}
    {u : α}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (hnew : actualWidthLabel L n S (J + 1))
    (hi : J + 1 ≤ i) :
    post.weight i = u * pre.weight i :=
  pre.weight_succ_current_eq_new_mul_of_ge hnew post u
    hpost.level_old hpost.var_old hpost.level_new hpost.var_new hi

end IntroducedLabelRecurrenceState.Case2SuppliedPostData

/-- Source-facing Case 2 recurrence-weight update from a supplied post-data
package and the corrected new-label certificate. -/
theorem CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    {state : IntroducedLabelRecurrenceState L n S J α}
    {state' : IntroducedLabelRecurrenceState L n S (J + 1) α}
    {u : α}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData state state' u) :
    ∀ i, J + 1 ≤ i → state'.weight i = u * state.weight i :=
  fun i hi ↦
    hpost.weight_succ_current_eq_new_mul_of_ge (i := i) hnew.introduced.1 hi

/-- If no label in a finite set has level `r`, the level-product factor is `1`. -/
theorem levelProductStep_eq_one_of_forall_ne
    {β : Type*} (labels : Finset β) (level : β → ℕ) (var : β → α) (r : ℕ)
    (h : ∀ p, p ∈ labels → level p ≠ r) :
    levelProductStep labels level var r = 1 := by
  rw [levelProductStep]
  exact Finset.prod_eq_one (fun p hp ↦ by
    rw [Finset.mem_filter] at hp
    exact False.elim ((h p hp.1) hp.2))

/-- A finite label gap over an interval makes every corresponding recurrence
factor `1`. -/
theorem levelProductStep_eq_one_of_gap
    {β : Type*} (labels : Finset β) (level : β → ℕ) (var : β → α)
    {a b r : ℕ}
    (hgap : ∀ p, p ∈ labels → ¬ (a ≤ level p ∧ level p < b))
    (har : a ≤ r) (hrb : r < b) :
    levelProductStep labels level var r = 1 := by
  refine levelProductStep_eq_one_of_forall_ne labels level var r ?_
  intro p hp hlevel
  exact hgap p hp ⟨by simpa [hlevel], by simpa [hlevel]⟩

/-- The level-product factor over the finite introduced-label domain is `1`
through a Case 2 gap interval when every introduced label avoids that interval. -/
theorem levelProductStep_introducedLabelFinset_eq_one_of_gap
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (level : ℕ → ℕ → ℕ) (var : ℕ → ℕ → α) {r : ℕ}
    (hgap : ∀ {s k}, introducedLabel L n S J s k →
      ¬ (J + 1 ≤ level s k ∧ level s k < prefixMinNat n S))
    (hrJ : J + 1 ≤ r) (hrS : r < prefixMinNat n S) :
    levelProductStep (introducedLabelFinset L n S J)
        (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
        (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2) r = 1 := by
  refine levelProductStep_eq_one_of_gap
    (introducedLabelFinset L n S J)
    (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2) ?_ hrJ hrS
  intro p hp
  exact hgap ((mem_introducedLabelFinset.mp hp))

namespace IntroducedLabelRecurrenceState

/-- In a Case 2 gap, every recurrence factor in the gap interval is `1`. -/
theorem step_eq_one_of_case2Gap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (hgap : state.case2Gap) {r : ℕ}
    (hrJ : J + 1 ≤ r) (hrS : r < prefixMinNat n S) :
    state.step r = 1 :=
  levelProductStep_introducedLabelFinset_eq_one_of_gap
    L n S J state.level state.var hgap hrJ hrS

end IntroducedLabelRecurrenceState

/-- In displayed Case 2, a gap of trivial recurrence factors over
`J+1..mu_S-1` makes every residual row weight equal to the pivot row weight. -/
theorem case2ResidualRow_monomialRec_eq_pivot_of_gap
    (step : ℕ → α) (n : ℕ → ℕ) (S J : ℕ)
    (hgap : ∀ k, J + 1 ≤ k → k < prefixMinNat n S → step k = 1)
    (i : Case2ResidualRowIndex n S J) :
    monomialRec step (case2ResidualRowLevel n S J i) =
      monomialRec step (J + 1) := by
  have hle : J + 1 ≤ case2ResidualRowLevel n S J i :=
    case2ResidualRowLevel_ge n S J i
  have hupper : case2ResidualRowLevel n S J i ≤ prefixMinNat n S :=
    ((mem_case2ResidualBlockRows n S J i.1).mp i.2).2
  exact monomialRec_eq_of_step_eq_one_on_Ico step hle
    (fun k hk hkrow ↦ hgap k hk (lt_of_lt_of_le hkrow hupper))

/-- Displayed Case 2 row weights are flat when the monomial recurrence factors
come from a finite label product with no labels in the Case 2 gap interval. -/
theorem case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap
    {β : Type*} (labels : Finset β) (level : β → ℕ) (var : β → α)
    (n : ℕ → ℕ) (S J : ℕ)
    (hgap : ∀ p, p ∈ labels →
      ¬ (J + 1 ≤ level p ∧ level p < prefixMinNat n S))
    (i : Case2ResidualRowIndex n S J) :
    monomialRec (levelProductStep labels level var)
        (case2ResidualRowLevel n S J i) =
      monomialRec (levelProductStep labels level var) (J + 1) := by
  refine case2ResidualRow_monomialRec_eq_pivot_of_gap
    (levelProductStep labels level var) n S J ?_ i
  intro k hk hkS
  exact levelProductStep_eq_one_of_gap labels level var hgap hk hkS

/-- Displayed Case 2 row weights are flat when the finite product is taken over
Lean's introduced-label domain and all introduced labels avoid the Case 2 gap. -/
theorem case2ResidualRow_introducedLabel_monomialRec_eq_pivot_of_gap
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (level : ℕ → ℕ → ℕ) (var : ℕ → ℕ → α)
    (hgap : ∀ {s k}, introducedLabel L n S J s k →
      ¬ (J + 1 ≤ level s k ∧ level s k < prefixMinNat n S))
    (i : Case2ResidualRowIndex n S J) :
    monomialRec
        (levelProductStep (introducedLabelFinset L n S J)
          (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
          (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2))
        (case2ResidualRowLevel n S J i) =
      monomialRec
        (levelProductStep (introducedLabelFinset L n S J)
          (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
          (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2)) (J + 1) := by
  refine case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap
    (introducedLabelFinset L n S J)
    (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2) n S J ?_ i
  intro p hp
  exact hgap ((mem_introducedLabelFinset.mp hp))

namespace IntroducedLabelRecurrenceState

/-- Displayed Case 2 residual rows have the same packaged recurrence weight as
the pivot row under the packaged Case 2 gap. -/
theorem case2ResidualRow_weight_eq_pivot_of_case2Gap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (hgap : state.case2Gap) (i : Case2ResidualRowIndex n S J) :
    state.weight (case2ResidualRowLevel n S J i) = state.weight (J + 1) := by
  exact case2ResidualRow_introducedLabel_monomialRec_eq_pivot_of_gap
    L n S J state.level state.var hgap i

/-- The named displayed Case 2 residual-row weight is flat across the residual
rows under the packaged Case 2 gap. -/
theorem case2ResidualRowWeight_eq_pivot_of_case2Gap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (hgap : state.case2Gap) (i : Case2ResidualRowIndex n S J) :
    state.case2ResidualRowWeight i = state.weight (J + 1) :=
  state.case2ResidualRow_weight_eq_pivot_of_case2Gap hgap i

/-- The named displayed Case 2 residual-row weight is flat relative to the
displayed pivot row under the packaged Case 2 gap. -/
theorem case2ResidualRowWeight_eq_displayedPivot_of_case2Gap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J α)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hgap : state.case2Gap) (i : Case2ResidualRowIndex n S J) :
    state.case2ResidualRowWeight i =
      state.case2ResidualRowWeight (case2DisplayedPivotRow n hS hcont) := by
  rw [state.case2ResidualRowWeight_eq_pivot_of_case2Gap hgap i,
    state.case2ResidualRowWeight_eq_pivot_of_case2Gap hgap
      (case2DisplayedPivotRow n hS hcont)]

end IntroducedLabelRecurrenceState

namespace IntroducedLabelRecurrenceState.Case2SuppliedPostData

/-- Under the old Case 2 gap, supplied successor weights are flat on the old
displayed residual rows after the common selected-variable multiplication. -/
theorem weight_succ_current_residual_flat_of_preGap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {pre : IntroducedLabelRecurrenceState L n S J α}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) α}
    {u : α}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (hnew : actualWidthLabel L n S (J + 1))
    (hgap : pre.case2Gap) (i : Case2ResidualRowIndex n S J) :
    post.weight (case2ResidualRowLevel n S J i) = post.weight (J + 1) := by
  have hupdate : ∀ i, J + 1 ≤ i → post.weight i = u * pre.weight i := by
    intro r hr
    exact hpost.weight_succ_current_eq_new_mul_of_ge (i := r) hnew hr
  rw [hupdate (case2ResidualRowLevel n S J i) (case2ResidualRowLevel_ge n S J i),
    hupdate (J + 1) le_rfl,
    pre.case2ResidualRow_weight_eq_pivot_of_case2Gap hgap i]

end IntroducedLabelRecurrenceState.Case2SuppliedPostData

/-- Source-facing consequence of the Case 2 recurrence-weight update: if the old
state satisfies the Case 2 gap, then the supplied successor weights are flat
across the old displayed residual rows after the common multiplication by the
new selected variable. -/
theorem CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (state : IntroducedLabelRecurrenceState L n S J α)
    (state' : IntroducedLabelRecurrenceState L n S (J + 1) α)
    (u : α)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.level s k = state.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → state'.var s k = state.var s k)
    (hlevel_new : state'.level S (J + 1) = J)
    (hvar_new : state'.var S (J + 1) = u)
    (hgap : state.case2Gap) (i : Case2ResidualRowIndex n S J) :
    state'.weight (case2ResidualRowLevel n S J i) = state'.weight (J + 1) := by
  have hupdate :=
    hnew.case2_weight_succ_current_eq_newVar_mul state state' u
      hlevel_old hvar_old hlevel_new hvar_new
  rw [hupdate (case2ResidualRowLevel n S J i) (case2ResidualRowLevel_ge n S J i),
    hupdate (J + 1) le_rfl,
    state.case2ResidualRow_weight_eq_pivot_of_case2Gap hgap i]

namespace CorrectedCase2NewLabelCertificate

/-- Source-facing residual-flat consequence from a supplied post-data package. -/
theorem case2_weight_succ_current_residual_flat_of_preGap_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    {state : IntroducedLabelRecurrenceState L n S J α}
    {state' : IntroducedLabelRecurrenceState L n S (J + 1) α}
    {u : α}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData state state' u)
    (hgap : state.case2Gap) (i : Case2ResidualRowIndex n S J) :
    state'.weight (case2ResidualRowLevel n S J i) = state'.weight (J + 1) :=
  hpost.weight_succ_current_residual_flat_of_preGap hnew.introduced.1 hgap i

end CorrectedCase2NewLabelCertificate

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

/-- The weighted pivot row-operation matrix is a unit.  This is only the
unitriangular finite-matrix fact, not a chart regularity or Jacobian theorem. -/
theorem weightedPivotBlockRowOp_isUnit (q x : ρ → R) :
    IsUnit (weightedPivotBlockRowOp q x) := by
  change IsUnit (fromBlocks (1 : Matrix Unit Unit R) 0
    (fun i _ ↦ -(q i * x i)) (1 : Matrix ρ ρ R))
  exact (Matrix.isUnit_fromBlocks_zero₁₂).2 ⟨isUnit_one, isUnit_one⟩

/-- The determinant of the weighted pivot row-operation matrix is a unit. -/
theorem weightedPivotBlockRowOp_det_isUnit (q x : ρ → R) :
    IsUnit (weightedPivotBlockRowOp q x).det :=
  (Matrix.isUnit_iff_isUnit_det (A := weightedPivotBlockRowOp q x)).mp
    (weightedPivotBlockRowOp_isUnit q x)

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

/-- The lower rows of a weighted pivot product are the lower-row diagonal
weights times the unweighted lower rows. -/
theorem weightedPivotDiagonal_mul_lowerRows
    {τ : Type*} [Fintype κ]
    (b0 : R) (b : ρ → R)
    (M : Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R)
    (C : Matrix (Unit ⊕ κ) τ R) :
    (((weightedPivotDiagonal b0 b * M) * C).submatrix Sum.inr id) =
      diagonal b * ((M * C).submatrix Sum.inr id) := by
  ext i t
  simp [weightedPivotDiagonal, Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type]

/-- Reindexed form of `weightedPivotDiagonal_mul_lowerRows`. -/
theorem weightedPivotDiagonal_mul_lowerRows_reindex
    {ρ' τ : Type*} [Fintype ρ'] [DecidableEq ρ'] [Fintype κ]
    (e : ρ' ≃ ρ) (b0 : R) (b : ρ → R)
    (M : Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R)
    (C : Matrix (Unit ⊕ κ) τ R) :
    (((weightedPivotDiagonal b0 b * M) * C).submatrix (fun i : ρ' ↦ Sum.inr (e i)) id) =
      diagonal (fun i : ρ' ↦ b (e i)) *
        ((M * C).submatrix (fun i : ρ' ↦ Sum.inr (e i)) id) := by
  have h := weightedPivotDiagonal_mul_lowerRows b0 b M C
  ext i t
  have hentry := congrFun (congrFun h (e i)) t
  simpa [Matrix.diagonal_mul] using hentry

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

/-- Stack two matrices with the same column type as top and bottom row blocks. -/
def verticalBlock {ι κ τ R : Type*}
    (top : Matrix ι τ R) (bottom : Matrix κ τ R) : Matrix (ι ⊕ κ) τ R :=
  Sum.elim top bottom

@[simp] theorem verticalBlock_inl {ι κ τ R : Type*}
    (top : Matrix ι τ R) (bottom : Matrix κ τ R) (i : ι) (j : τ) :
    verticalBlock top bottom (Sum.inl i) j = top i j :=
  rfl

@[simp] theorem verticalBlock_inr {ι κ τ R : Type*}
    (top : Matrix ι τ R) (bottom : Matrix κ τ R) (i : κ) (j : τ) :
    verticalBlock top bottom (Sum.inr i) j = bottom i j :=
  rfl

/-- Multiplying a vertical block by a block-diagonal matrix acts separately on
the top and bottom blocks. -/
theorem fromBlocks_mul_verticalBlock
    {ι κ ρ τ R : Type*} [Semiring R] [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (D : Matrix ρ κ R)
    (Ctop : Matrix ι τ R) (Ctail : Matrix κ τ R) :
    fromBlocks A 0 0 D * verticalBlock Ctop Ctail =
      verticalBlock (A * Ctop) (D * Ctail) := by
  ext r t
  rcases r with i | k
  · simp [verticalBlock, Matrix.mul_apply, Fintype.sum_sum_type]
  · simp [verticalBlock, Matrix.mul_apply, Fintype.sum_sum_type]

/-- A tail product identity lifts through an unchanged top block. -/
theorem fromBlocks_mul_verticalBlock_eq_of_tail
    {ι κ ρ τ R : Type*} [Semiring R] [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (L Rtail : Matrix ρ κ R)
    (Ctop : Matrix ι τ R) (Ctail Ctail' : Matrix κ τ R)
    (h : L * Ctail = Rtail * Ctail') :
    fromBlocks A 0 0 L * verticalBlock Ctop Ctail =
      fromBlocks A 0 0 Rtail * verticalBlock Ctop Ctail' := by
  rw [fromBlocks_mul_verticalBlock, fromBlocks_mul_verticalBlock, h]

/-- A pivot-only cleared block keeps the top following-factor row and kills
the lower following-factor block.  This is block multiplication only. -/
theorem weightedPivotClearedBlock_zero_mul_verticalBlock
    {ρ κ τ R : Type*} [CommRing R] [Fintype κ]
    (Ctop : Matrix Unit τ R) (Ctail : Matrix κ τ R) :
    weightedPivotClearedBlock (0 : Matrix ρ κ R) * verticalBlock Ctop Ctail =
      verticalBlock Ctop (0 : Matrix ρ τ R) := by
  rw [weightedPivotClearedBlock, fromBlocks_mul_verticalBlock]
  ext i j
  rcases i with (_ | i)
  · simp [verticalBlock]
  · simp [verticalBlock]

/-- Multiplying a cleared pivot block by a split following factor keeps the
pivot row and multiplies the lower-right block by the following tail.  This is
finite block algebra only, not a transition theorem. -/
theorem weightedPivotClearedBlock_mul_verticalBlock
    {ρ κ τ R : Type*} [CommRing R] [Fintype κ]
    (D : Matrix ρ κ R) (Ctop : Matrix Unit τ R) (Ctail : Matrix κ τ R) :
    weightedPivotClearedBlock D * verticalBlock Ctop Ctail =
      verticalBlock Ctop (D * Ctail) := by
  rw [weightedPivotClearedBlock, fromBlocks_mul_verticalBlock]
  ext i j
  rcases i with (_ | i)
  · simp [verticalBlock]
  · simp [verticalBlock]

section ColumnOperationBlocks

variable {R ρ κ τ : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]

/-- The pre-`Q` pivot block, with top row `[1 y]`. -/
def pivotPreQBlock (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R) :
    Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R :=
  fromBlocks 1 y x D

/-- Indices other than a chosen pivot. -/
abbrev pivotComplement {ι : Type*} (pivot : ι) := {i : ι // i ≠ pivot}

/-- Deleting the displayed pivot row from the old residual-row subtype is the
same finite type as the post-pivot row range `J+2..M(S)`. -/
noncomputable def case2DisplayedPivotRowComplementEquivPostPivotRows
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    pivotComplement (case2DisplayedPivotRow n hS hcont) ≃
      (case2PostPivotRows n S J : Type) where
  toFun i :=
    ⟨i.1.1, by
      rw [mem_case2PostPivotRows]
      have hi := (mem_case2ResidualBlockRows n S J i.1.1).mp i.1.2
      have hne : i.1.1 ≠ J + 1 := by
        intro h
        exact i.2 (Subtype.ext h)
      omega⟩
  invFun i :=
    ⟨⟨i.1, by
        rw [mem_case2ResidualBlockRows]
        have hi := (mem_case2PostPivotRows n S J i.1).mp i.2
        exact ⟨by omega, hi.2⟩⟩, by
      intro h
      have hval : i.1 = J + 1 := by
        exact congrArg Subtype.val h
      have hi := (mem_case2PostPivotRows n S J i.1).mp i.2
      omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- Deleting the displayed pivot row from the old residual-row subtype is the
same finite type as the next same-stage residual-row index type. -/
noncomputable def case2DisplayedPivotRowComplementEquivResidualRowSucc
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    pivotComplement (case2DisplayedPivotRow n hS hcont) ≃
      Case2ResidualRowIndex n S (J + 1) where
  toFun i :=
    ⟨i.1.1, by
      rw [mem_case2ResidualBlockRows]
      have hi := (mem_case2ResidualBlockRows n S J i.1.1).mp i.1.2
      have hne : i.1.1 ≠ J + 1 := by
        intro h
        exact i.2 (Subtype.ext h)
      omega⟩
  invFun i :=
    ⟨⟨i.1, by
        rw [mem_case2ResidualBlockRows]
        have hi := (mem_case2ResidualBlockRows n S (J + 1) i.1).mp i.2
        exact ⟨by omega, hi.2⟩⟩, by
      intro h
      have hval : i.1 = J + 1 := by
        exact congrArg Subtype.val h
      have hi := (mem_case2ResidualBlockRows n S (J + 1) i.1).mp i.2
      omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

@[simp] theorem case2DisplayedPivotRowComplementEquivPostPivotRows_apply_coe
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (i : pivotComplement (case2DisplayedPivotRow n hS hcont)) :
    ((case2DisplayedPivotRowComplementEquivPostPivotRows n hS hcont i : ℕ) =
      i.1.1) :=
  rfl

@[simp] theorem case2DisplayedPivotRowComplementEquivPostPivotRows_symm_apply_coe
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (i : (case2PostPivotRows n S J : Type)) :
    (((case2DisplayedPivotRowComplementEquivPostPivotRows n hS hcont).symm i).1.1 =
      i.1) :=
  rfl

/-- Deleting the displayed pivot column from the old residual-column subtype is
the same finite type as the post-pivot column range `J+2..M^(S+1)`. -/
noncomputable def case2DisplayedPivotColComplementEquivPostPivotCols
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    pivotComplement (case2DisplayedPivotCol n hS hcont) ≃
      (case2PostPivotCols n S J : Type) where
  toFun j :=
    ⟨j.1.1, by
      rw [mem_case2PostPivotCols]
      have hj := (mem_case2ResidualBlockCols n S J j.1.1).mp j.1.2
      have hne : j.1.1 ≠ J + 1 := by
        intro h
        exact j.2 (Subtype.ext h)
      omega⟩
  invFun j :=
    ⟨⟨j.1, by
        rw [mem_case2ResidualBlockCols]
        have hj := (mem_case2PostPivotCols n S J j.1).mp j.2
        exact ⟨by omega, hj.2⟩⟩, by
      intro h
      have hval : j.1 = J + 1 := by
        exact congrArg Subtype.val h
      have hj := (mem_case2PostPivotCols n S J j.1).mp j.2
      omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    rfl

/-- Deleting the displayed pivot column from the old residual-column subtype is
the same finite type as the next same-stage residual-column index type. -/
noncomputable def case2DisplayedPivotColComplementEquivResidualColSucc
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    pivotComplement (case2DisplayedPivotCol n hS hcont) ≃
      Case2ResidualColIndex n S (J + 1) where
  toFun j :=
    ⟨j.1.1, by
      rw [mem_case2ResidualBlockCols]
      have hj := (mem_case2ResidualBlockCols n S J j.1.1).mp j.1.2
      have hne : j.1.1 ≠ J + 1 := by
        intro h
        exact j.2 (Subtype.ext h)
      omega⟩
  invFun j :=
    ⟨⟨j.1, by
        rw [mem_case2ResidualBlockCols]
        have hj := (mem_case2ResidualBlockCols n S (J + 1) j.1).mp j.2
        exact ⟨by omega, hj.2⟩⟩, by
      intro h
      have hval : j.1 = J + 1 := by
        exact congrArg Subtype.val h
      have hj := (mem_case2ResidualBlockCols n S (J + 1) j.1).mp j.2
      omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    rfl

@[simp] theorem case2DisplayedPivotColComplementEquivPostPivotCols_apply_coe
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (j : pivotComplement (case2DisplayedPivotCol n hS hcont)) :
    ((case2DisplayedPivotColComplementEquivPostPivotCols n hS hcont j : ℕ) =
      j.1.1) :=
  rfl

@[simp] theorem case2DisplayedPivotColComplementEquivPostPivotCols_symm_apply_coe
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (j : (case2PostPivotCols n S J : Type)) :
    (((case2DisplayedPivotColComplementEquivPostPivotCols n hS hcont).symm j).1.1 =
      j.1) :=
  rfl

@[simp] theorem case2DisplayedPivotRowComplementEquivResidualRowSucc_apply_coe
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (i : pivotComplement (case2DisplayedPivotRow n hS hcont)) :
    ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont i : ℕ) =
      i.1.1) :=
  rfl

@[simp] theorem case2DisplayedPivotRowComplementEquivResidualRowSucc_symm_apply_coe
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (i : Case2ResidualRowIndex n S (J + 1)) :
    (((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i).1.1 =
      i.1) :=
  rfl

@[simp] theorem case2DisplayedPivotColComplementEquivResidualColSucc_apply_coe
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (j : pivotComplement (case2DisplayedPivotCol n hS hcont)) :
    ((case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont j : ℕ) =
      j.1.1) :=
  rfl

@[simp] theorem case2DisplayedPivotColComplementEquivResidualColSucc_symm_apply_coe
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (j : Case2ResidualColIndex n S (J + 1)) :
    (((case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont).symm j).1.1 =
      j.1) :=
  rfl

theorem case2DisplayedPivotRowComplement_isEmpty_iff_postPivotRows_isEmpty
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    IsEmpty (pivotComplement (case2DisplayedPivotRow n hS hcont)) ↔
      IsEmpty (case2PostPivotRows n S J : Type) := by
  let e := case2DisplayedPivotRowComplementEquivPostPivotRows n hS hcont
  constructor
  · intro h
    exact ⟨fun i ↦ h.false (e.symm i)⟩
  · intro h
    exact ⟨fun i ↦ h.false (e i)⟩

theorem case2DisplayedPivotColComplement_isEmpty_iff_postPivotCols_isEmpty
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    IsEmpty (pivotComplement (case2DisplayedPivotCol n hS hcont)) ↔
      IsEmpty (case2PostPivotCols n S J : Type) := by
  let e := case2DisplayedPivotColComplementEquivPostPivotCols n hS hcont
  constructor
  · intro h
    exact ⟨fun j ↦ h.false (e.symm j)⟩
  · intro h
    exact ⟨fun j ↦ h.false (e j)⟩

theorem case2DisplayedPivotRowComplement_isEmpty_of_postPivotRows_eq_empty
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hrows : case2PostPivotRows n S J = ∅) :
    IsEmpty (pivotComplement (case2DisplayedPivotRow n hS hcont)) := by
  let e := case2DisplayedPivotRowComplementEquivPostPivotRows n hS hcont
  refine ⟨fun i ↦ ?_⟩
  have hempty : (e i).1 ∈ (∅ : Finset ℕ) := by
    simpa [hrows] using (e i).2
  exact (Finset.notMem_empty (e i).1) hempty

/-- Current-prefix row exhaustion empties the displayed pivot's row
complement.

This identifies the row-exhausted side of the stopped displayed Case 2
terminal branch.  It is independent of actual-width column exhaustion and is
finite-domain bookkeeping, not construction of the next following matrix. -/
theorem case2DisplayedPivotRowComplement_isEmpty_of_prefixMin_current_eq
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hrow : prefixMinNat n S = J + 1) :
    IsEmpty (pivotComplement (case2DisplayedPivotRow n hS hcont)) :=
  case2DisplayedPivotRowComplement_isEmpty_of_postPivotRows_eq_empty hS hcont
    (case2PostPivotRows_eq_empty_of_prefixMin_current_eq hrow)

theorem case2DisplayedPivotColComplement_isEmpty_of_postPivotCols_eq_empty
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hcols : case2PostPivotCols n S J = ∅) :
    IsEmpty (pivotComplement (case2DisplayedPivotCol n hS hcont)) := by
  let e := case2DisplayedPivotColComplementEquivPostPivotCols n hS hcont
  refine ⟨fun j ↦ ?_⟩
  have hempty : (e j).1 ∈ (∅ : Finset ℕ) := by
    simpa [hcols] using (e j).2
  exact (Finset.notMem_empty (e j).1) hempty

/-- Actual next-width exhaustion empties the displayed pivot's column
complement.

This identifies the exhausted side of the stopped displayed Case 2 terminal
branch.  It is finite-domain bookkeeping, not construction of the next
following matrix. -/
theorem case2DisplayedPivotColComplement_isEmpty_of_width_next_eq
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1) :
    IsEmpty (pivotComplement (case2DisplayedPivotCol n hS hcont)) :=
  case2DisplayedPivotColComplement_isEmpty_of_postPivotCols_eq_empty hS hcont
    (case2PostPivotCols_eq_empty_of_width_next_eq hwidth)

/-- When the next Case 2 continuation bound fails, one of the displayed
pivot-complement index types is empty.  This is the finite-index content
behind the terminal one-row/one-column shape, not the `S+1` advance
transition. -/
theorem case2DisplayedPivotComplement_isEmpty_or_isEmpty_of_not_next_cont
    {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1)) :
    IsEmpty (pivotComplement (case2DisplayedPivotRow n hS hcont)) ∨
      IsEmpty (pivotComplement (case2DisplayedPivotCol n hS hcont)) := by
  rcases case2PostPivotRows_empty_or_cols_empty_of_not_next_cont hS hstop with
    hrows | hcols
  · exact Or.inl
      (case2DisplayedPivotRowComplement_isEmpty_of_postPivotRows_eq_empty
        hS hcont hrows)
  · exact Or.inr
      (case2DisplayedPivotColComplement_isEmpty_of_postPivotCols_eq_empty
        hS hcont hcols)

/-- If the next Case 2 continuation bound fails, then every lower-right matrix
on the displayed pivot-complement row and column types is equal to every other.
This is only domain-vacuity bookkeeping for the lower-right complement block,
not the full `D'''_J = (1,0,...)` terminal block statement. -/
theorem case2DisplayedPivotComplement_matrix_subsingleton_of_not_next_cont
    {K : Type*} {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1)) :
    Subsingleton
      (Matrix (pivotComplement (case2DisplayedPivotRow n hS hcont))
        (pivotComplement (case2DisplayedPivotCol n hS hcont)) K) := by
  rcases case2DisplayedPivotComplement_isEmpty_or_isEmpty_of_not_next_cont
      hS hcont hstop with hrow | hcol
  · refine ⟨fun A B ↦ ?_⟩
    ext i j
    exact False.elim (hrow.false i)
  · refine ⟨fun A B ↦ ?_⟩
    ext i j
    exact False.elim (hcol.false j)

/-- Under failed next continuation, the lower-right displayed pivot-complement
matrix is the zero matrix.  This is a consequence of empty row or column
complement type, not a proof of Aoyagi's full terminal `D'''` shape. -/
theorem case2DisplayedPivotComplement_matrix_eq_zero_of_not_next_cont
    {K : Type*} [Zero K] {n : ℕ → ℕ} {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (D : Matrix (pivotComplement (case2DisplayedPivotRow n hS hcont))
      (pivotComplement (case2DisplayedPivotCol n hS hcont)) K) :
    D = 0 :=
  (case2DisplayedPivotComplement_matrix_subsingleton_of_not_next_cont
    (K := K) hS hcont hstop).elim D 0

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

/-- After a selected-entry substitution, pivot-first reindexing identifies the
row-weighted source block with the normalised block whose row weights include
the selected variable. This is finite matrix algebra only. -/
theorem pivotFirst_diagonal_mul_selectedEntrySubstitutionMatrix
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {rowPivot : ι} {colPivot : κ}
    (u : R) (weight : ι → R) (residual : ι → κ → R) :
    (diagonal weight *
        selectedEntrySubstitutionMatrix rowPivot colPivot u residual).submatrix
        (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot) =
      weightedPivotDiagonal (u * weight rowPivot)
        (fun i : pivotComplement rowPivot ↦ u * weight i.1) *
        pivotFirstMatrix rowPivot colPivot
          (selectedEntryNormalizedMatrix rowPivot colPivot residual) := by
  rw [diagonal_mul_selectedEntrySubstitutionMatrix]
  rw [weightedPivotDiagonal_eq_pivotFirst_diagonal rowPivot (fun i ↦ u * weight i)]
  rw [pivotFirstMatrix]
  rw [Matrix.submatrix_mul_equiv
    (diagonal (fun i ↦ u * weight i))
    (selectedEntryNormalizedMatrix rowPivot colPivot residual)
    (pivotFirstIndexEquiv rowPivot)
    (pivotFirstIndexEquiv rowPivot)
    (pivotFirstIndexEquiv colPivot)]

/-- The elementary right column operation that clears the pivot row off the pivot. -/
def pivotQ (y : Matrix Unit κ R) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R :=
  fromBlocks 1 (-y) 0 1

/-- The pivot `Q` column-operation matrix is a unit.  This is the
unitriangular finite-matrix fact only. -/
theorem pivotQ_isUnit (y : Matrix Unit κ R) : IsUnit (pivotQ y) := by
  change IsUnit (fromBlocks (1 : Matrix Unit Unit R) (-y) 0 (1 : Matrix κ κ R))
  exact (Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩

/-- The determinant of the pivot `Q` column-operation matrix is a unit. -/
theorem pivotQ_det_isUnit (y : Matrix Unit κ R) : IsUnit (pivotQ y).det :=
  (Matrix.isUnit_iff_isUnit_det (A := pivotQ y)).mp (pivotQ_isUnit y)

/-- The inverse elementary column operation. -/
def pivotQinv (y : Matrix Unit κ R) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R :=
  fromBlocks 1 y 0 1

/-- The displayed inverse `Q⁻¹` column-operation matrix is a unit.  This is the
unitriangular finite-matrix fact only. -/
theorem pivotQinv_isUnit (y : Matrix Unit κ R) : IsUnit (pivotQinv y) := by
  change IsUnit (fromBlocks (1 : Matrix Unit Unit R) y 0 (1 : Matrix κ κ R))
  exact (Matrix.isUnit_fromBlocks_zero₂₁).2 ⟨isUnit_one, isUnit_one⟩

/-- The determinant of the displayed inverse `Q⁻¹` column-operation matrix is a
unit. -/
theorem pivotQinv_det_isUnit (y : Matrix Unit κ R) : IsUnit (pivotQinv y).det :=
  (Matrix.isUnit_iff_isUnit_det (A := pivotQinv y)).mp (pivotQinv_isUnit y)

/-- Top row of the inverse pivot column operation applied to a following
factor. -/
theorem pivotQinv_mul_top_apply
    {κ τ R : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]
    (y : Matrix Unit κ R) (C : Matrix (Unit ⊕ κ) τ R) (a : τ) :
    (pivotQinv y * C) (Sum.inl ()) a =
      C (Sum.inl ()) a + ∑ j : κ, y () j * C (Sum.inr j) a := by
  simp [pivotQinv, Matrix.mul_apply, Fintype.sum_sum_type]

/-- Lower rows of the inverse pivot column operation are unchanged. -/
theorem pivotQinv_mul_tail_apply
    {κ τ R : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]
    (y : Matrix Unit κ R) (C : Matrix (Unit ⊕ κ) τ R) (i : κ) (a : τ) :
    (pivotQinv y * C) (Sum.inr i) a = C (Sum.inr i) a := by
  let Ctail : Matrix κ τ R := fun i a ↦ C (Sum.inr i) a
  suffices (∑ x, (1 : Matrix κ κ R) i x * Ctail x a) = Ctail i a by
    simpa [pivotQinv, Matrix.mul_apply, Fintype.sum_sum_type, Ctail] using this
  simpa [Ctail, Matrix.mul_apply] using
    congrArg (fun M : Matrix κ τ R ↦ M i a) (Matrix.one_mul Ctail)

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

/-- Supplied data for the source-displayed top-left pivot calculation after
the selected chart has already been transported to pivot-first coordinates.

`weightedSource` is an already weighted, already source-substituted block.  The
field `source_eq` is the only bridge to the normalised pivot block used by the
finite `Q/P` algebra.  This structure does not construct a selected-entry
chart, prove atlas coverage, produce recurrence/exponent post-data, or assert
that a Case 1 or Case 2 transition has occurred. -/
structure WeightedPivotFirstSubstitutionData
    (R ρ κ τ : Type*) [CommRing R] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] [DecidableEq κ] where
  b0 : R
  b : ρ → R
  q : ρ → R
  x : Matrix ρ Unit R
  y : Matrix Unit κ R
  D : Matrix ρ κ R
  weightedSource : Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R
  C : Matrix (Unit ⊕ κ) τ R
  source_eq :
    weightedSource = weightedPivotDiagonal b0 b * pivotPreQBlock x y D
  quotient : ∀ i, b i = q i * b0

namespace WeightedPivotFirstSubstitutionData

/-- Source-order form of the displayed top-left `Q/P` identity from supplied
pivot-first substitution data.  The selected chart, source-coordinate
transport, row-weight transport, and quotient witnesses are all hypotheses
packaged in `data`. -/
theorem sourceOrder_identity
    {R ρ κ τ : Type*} [CommRing R] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] [DecidableEq κ]
    (data : WeightedPivotFirstSubstitutionData R ρ κ τ) :
    (weightedPivotBlockRowOp data.q (fun i ↦ data.x i ()) * data.weightedSource) *
        data.C =
      (weightedPivotDiagonal data.b0 data.b *
          weightedPivotClearedBlock (data.D - data.x * data.y)) *
        (pivotQinv data.y * data.C) := by
  rw [data.source_eq]
  rw [← Matrix.mul_assoc]
  exact weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul
    data.b0 data.b data.q data.x data.y data.D data.C data.quotient

end WeightedPivotFirstSubstitutionData

/-- Source-order displayed top-left `Q/P` identity with quotient witnesses
chosen from divisibility of the lower row weights by the pivot row weight.

The weighted source block is supplied by `hsource`; this theorem does not
construct the selected-entry chart or prove any Case 1/Case 2 transition
post-data. -/
theorem exists_weightedPivotFirstSubstitution_sourceOrder_identity_of_forall_dvd
    [Fintype ρ] [DecidableEq ρ]
    (b0 : R) (b : ρ → R)
    (x : Matrix ρ Unit R) (y : Matrix Unit κ R) (D : Matrix ρ κ R)
    (weightedSource : Matrix (Unit ⊕ ρ) (Unit ⊕ κ) R)
    (C : Matrix (Unit ⊕ κ) τ R)
    (hsource :
      weightedSource = weightedPivotDiagonal b0 b * pivotPreQBlock x y D)
    (hdiv : ∀ i, b0 ∣ b i) :
    ∃ q : ρ → R,
      (weightedPivotBlockRowOp q (fun i ↦ x i ()) * weightedSource) * C =
        (weightedPivotDiagonal b0 b * weightedPivotClearedBlock (D - x * y)) *
          (pivotQinv y * C) := by
  rcases exists_right_quotients_of_forall_dvd hdiv with ⟨q, hq⟩
  exact ⟨q,
      (WeightedPivotFirstSubstitutionData.sourceOrder_identity
      ({ b0 := b0
         b := b
         q := q
         x := x
         y := y
         D := D
         weightedSource := weightedSource
         C := C
         source_eq := hsource
         quotient := hq } :
        WeightedPivotFirstSubstitutionData R ρ κ τ))⟩

/-- Left multiplication by a diagonal matrix weights each row. -/
theorem diagonal_mul_apply
    {ι κ R : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
    (weight : ι → R) (A : Matrix ι κ R) (i : ι) (j : κ) :
    (diagonal weight * A) i j = weight i * A i j := by
  exact Matrix.diagonal_mul weight A i j

/-- Case 1 row-strip source matrix from an already divided row-strip matrix
`A`.  It reconstructs the source entries as `u * A i j` on strip rows and
leaves lower residual rows unchanged.  In Case 1(1), `u` is the selected old
chart denominator; in displayed Case 1(2), `u` is the displayed row-strip
pivot.  This is only elementary row-wise source algebra, not a chart
construction. -/
def case1RowStripSourceMatrix
    {ι κ R : Type*} [CommRing R]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (A : Matrix ι κ R) : Matrix ι κ R :=
  fun i j ↦ if strip i then u * A i j else A i j

/-- Case 1(2) old row weights after the hidden old exceptional variable has
been factored as `old = u * old'`.  The row strip has not gained the old
factor, while lower residual rows have. -/
def case1RowStripOldWeight
    {ι R : Type*} [CommRing R]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (baseWeight : ι → R) : ι → R :=
  fun i ↦ if strip i then baseWeight i else u * baseWeight i

/-- Case 1(1) post row weights in the selected-old chart.  The selected old
chart variable is absorbed exactly on the divided row strip, while lower rows
keep their pre-chart weights. -/
def case1SelectedOldPostWeight
    {ι R : Type*} [CommRing R]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (baseWeight : ι → R) : ι → R :=
  fun i ↦ if strip i then u * baseWeight i else baseWeight i

/-- Canonical residual-row predicate for the Case 1 row strip: rows from
`J+1` through the old selected level `J+J1`.  The same finite predicate marks
the selected-old divided rows in Case 1(1) and the displayed divided rows in
Case 1(2); the chart denominator is supplied separately. -/
def case1ResidualRowStrip (n : ℕ → ℕ) (S J J1 : ℕ)
    (i : Case2ResidualRowIndex n S J) : Prop :=
  case2ResidualRowLevel n S J i ≤ J + J1

instance case1ResidualRowStrip_decidablePred
    (n : ℕ → ℕ) (S J J1 : ℕ) :
    DecidablePred (case1ResidualRowStrip n S J J1) :=
  fun i ↦ inferInstanceAs (Decidable (case2ResidualRowLevel n S J i ≤ J + J1))

/-- Source weights with the selected old factor still at level `h` are exactly
the row-strip convention: unchanged through level `h`, multiplied by `u`
below that strip. -/
theorem case1RowStripOldWeight_eq_monomialRec_mulStepAt_of_level
    {ι R : Type*} [CommRing R]
    (step : ℕ → R) (u : R) (h : ℕ) (level : ι → ℕ) :
    case1RowStripOldWeight (fun i ↦ level i ≤ h) u
        (fun i ↦ monomialRec step (level i)) =
      fun i ↦ monomialRec (mulStepAt step u h) (level i) := by
  funext i
  by_cases hi : level i ≤ h
  · simp [case1RowStripOldWeight, hi, monomialRec_mulStepAt_eq_of_le step u hi]
  · have hge : h + 1 ≤ level i := by omega
    simp [case1RowStripOldWeight, hi, monomialRec_mulStepAt_eq_mul_of_ge step u hge]

/-- Residual-row specialization of the source-weight convention for the
displayed Case 1(2) row strip. -/
theorem case1ResidualRowStripOldWeight_eq_sourceMulStepAt
    {R : Type*} [CommRing R]
    (step : ℕ → R) (u : R) (n : ℕ → ℕ) (S J J1 : ℕ) :
    case1RowStripOldWeight (case1ResidualRowStrip n S J J1) u
        (fun i ↦ monomialRec step (case2ResidualRowLevel n S J i)) =
      fun i ↦ monomialRec (mulStepAt step u (J + J1))
        (case2ResidualRowLevel n S J i) :=
  case1RowStripOldWeight_eq_monomialRec_mulStepAt_of_level
    step u (J + J1) (case2ResidualRowLevel n S J)

/-- Case 1(2) row-strip old-weight convention rewritten as substituted source
recurrence weights, under supplied same-domain old selected-variable
factorisation data.

The `source` recurrence is already the pullback after `old = u * old'`; this
does not construct that pullback from coordinates. -/
theorem case1ResidualRowStripOldWeight_eq_sourceWeight_of_selectedOldFactoredBase
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {vector : ℕ → ℕ → ℕ → ℤ}
    (data : IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData
      source factoredBase s0 k0 u)
    (hfirst :
      Case1FirstJumpHypotheses L n S J J1 s0 k0 factoredBase.level vector) :
    case1RowStripOldWeight (case1ResidualRowStrip n S J J1) u
        (fun i ↦ factoredBase.case2ResidualRowWeight i) =
      fun i ↦ source.weight (case2ResidualRowLevel n S J i) := by
  change case1RowStripOldWeight (case1ResidualRowStrip n S J J1) u
      (fun i ↦ monomialRec factoredBase.step (case2ResidualRowLevel n S J i)) =
    fun i ↦ monomialRec source.step (case2ResidualRowLevel n S J i)
  rw [case1ResidualRowStripOldWeight_eq_sourceMulStepAt factoredBase.step u n S J J1]
  rw [← data.step_eq_mulStepAt_of_firstJump hfirst]

/-- Elementary Case 1(2) row-strip weighting identity.

The selected variable is counted once on the right.  In strip rows it comes
from the divided matrix entries; below the strip it comes from the hidden
old-variable factorisation. -/
theorem case1RowStrip_diagonal_mul_sourceMatrix
    {ι κ R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (baseWeight : ι → R) (A : Matrix ι κ R) :
    diagonal (case1RowStripOldWeight strip u baseWeight) *
        case1RowStripSourceMatrix strip u A =
      diagonal (fun i ↦ u * baseWeight i) * A := by
  ext i j
  calc
    (diagonal (case1RowStripOldWeight strip u baseWeight) *
          case1RowStripSourceMatrix strip u A) i j
        = case1RowStripOldWeight strip u baseWeight i *
            case1RowStripSourceMatrix strip u A i j := by
            rw [diagonal_mul_apply]
    _ = (u * baseWeight i) * A i j := by
        by_cases hi : strip i
        · simp [case1RowStripOldWeight, case1RowStripSourceMatrix, hi]
          ring
        · simp [case1RowStripOldWeight, case1RowStripSourceMatrix, hi]
    _ = (diagonal (fun i ↦ u * baseWeight i) * A) i j := by
        rw [diagonal_mul_apply]

/-- Elementary Case 1(1) selected-old row-strip identity.

In the selected-old chart, strip entries are divided by the selected old
variable.  Equivalently, multiplying the source matrix by the pre-chart
diagonal weights is the same as multiplying the post-chart matrix by row
weights that have absorbed the selected old factor on precisely the strip
rows. -/
theorem case1SelectedOld_diagonal_mul_sourceMatrix
    {ι κ R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (baseWeight : ι → R) (A : Matrix ι κ R) :
    diagonal baseWeight * case1RowStripSourceMatrix strip u A =
      diagonal (case1SelectedOldPostWeight strip u baseWeight) * A := by
  ext i j
  calc
    (diagonal baseWeight * case1RowStripSourceMatrix strip u A) i j
        = baseWeight i * case1RowStripSourceMatrix strip u A i j := by
            rw [diagonal_mul_apply]
    _ = case1SelectedOldPostWeight strip u baseWeight i * A i j := by
        by_cases hi : strip i
        · simp [case1SelectedOldPostWeight, case1RowStripSourceMatrix, hi]
          ring
        · simp [case1SelectedOldPostWeight, case1RowStripSourceMatrix, hi]
    _ = (diagonal (case1SelectedOldPostWeight strip u baseWeight) * A) i j := by
        rw [diagonal_mul_apply]

/-- Residual-row form of the Case 1(1) selected-old recurrence-weight update.

Starting from a supplied base recurrence, the piecewise post-weight convention
on residual rows is exactly the recurrence obtained by lowering the selected
old factor from level `J+J1` to level `J`. -/
theorem case1SelectedOldPostWeight_eq_monomialRec_loweredLevel
    {R : Type*} [CommRing R]
    (step : ℕ → R) (u : R) (n : ℕ → ℕ) (S J J1 : ℕ) :
    case1SelectedOldPostWeight (case1ResidualRowStrip n S J J1) u
        (fun i ↦ monomialRec (mulStepAt step u (J + J1))
          (case2ResidualRowLevel n S J i)) =
      fun i ↦ monomialRec (mulStepAt step u J)
        (case2ResidualRowLevel n S J i) := by
  funext i
  simpa [case1SelectedOldPostWeight, case1ResidualRowStrip] using
    monomialRec_mulStepAt_case1_selectedOld_postWeight
      (step := step) (u := u) (J := J) (J1 := J1)
      (i := case2ResidualRowLevel n S J i)
      (case2ResidualRowLevel_ge n S J i)

/-- Case 1(1) row-strip source identity with the right diagonal written as the
lowered selected-old recurrence. -/
theorem case1SelectedOld_diagonal_mul_sourceMatrix_loweredLevel
    {R : Type*} [CommRing R]
    (step : ℕ → R) (u : R) (n : ℕ → ℕ) (S J J1 : ℕ)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R) :
    diagonal
        (fun i ↦ monomialRec (mulStepAt step u (J + J1))
          (case2ResidualRowLevel n S J i)) *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A =
      diagonal
        (fun i ↦ monomialRec (mulStepAt step u J)
          (case2ResidualRowLevel n S J i)) * A := by
  rw [case1SelectedOld_diagonal_mul_sourceMatrix]
  rw [case1SelectedOldPostWeight_eq_monomialRec_loweredLevel]

/-- Displayed Case 1(2) source-weight form of the row-strip identity.

The left diagonal is the original source recurrence after substituting the old
selected factor `old = u * old'` at level `J+J1`.  The right diagonal is the
factored-base recurrence with the common selected factor pulled to every
residual row from `J+1` onward. -/
theorem case1ResidualRowStrip_diagonal_mul_sourceMatrix_sourceWeights
    {R : Type*} [CommRing R]
    (step : ℕ → R) (u : R) (n : ℕ → ℕ) (S J J1 : ℕ)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R) :
    diagonal
        (fun i ↦ monomialRec (mulStepAt step u (J + J1))
          (case2ResidualRowLevel n S J i)) *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A =
      diagonal
        (fun i ↦ u * monomialRec step (case2ResidualRowLevel n S J i)) * A := by
  rw [← case1ResidualRowStripOldWeight_eq_sourceMulStepAt step u n S J J1]
  exact case1RowStrip_diagonal_mul_sourceMatrix
    (case1ResidualRowStrip n S J J1) u
    (fun i ↦ monomialRec step (case2ResidualRowLevel n S J i)) A

/-- Pivot-first form of the Case 1(2) row-strip weighting identity.  This is
the source-order input expected by the generic displayed top-left `Q/P`
adapter once a pivot row and column have already been chosen. -/
theorem case1RowStrip_diagonal_mul_sourceMatrix_pivotFirst
    {ι κ R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (baseWeight : ι → R) (A : Matrix ι κ R) :
    (diagonal (case1RowStripOldWeight strip u baseWeight) *
        case1RowStripSourceMatrix strip u A).submatrix
        (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot) =
      weightedPivotDiagonal (u * baseWeight rowPivot)
        (fun i : pivotComplement rowPivot ↦ u * baseWeight i.1) *
        pivotFirstMatrix rowPivot colPivot A := by
  rw [case1RowStrip_diagonal_mul_sourceMatrix]
  rw [← Matrix.submatrix_mul_equiv
    (diagonal (fun i ↦ u * baseWeight i))
    A
    (pivotFirstIndexEquiv rowPivot)
    (pivotFirstIndexEquiv rowPivot)
    (pivotFirstIndexEquiv colPivot)]
  rw [← weightedPivotDiagonal_eq_pivotFirst_diagonal rowPivot
    (fun i ↦ u * baseWeight i)]
  rw [pivotFirstMatrix]

/-- Case 1(2) row-strip source data, transported to pivot-first coordinates,
as a supplied instance of the generic displayed top-left adapter.  The
row-strip algebra is proved here; the selected chart, source validity of the
hidden old label, quotient regularity, and transition post-data remain
explicit inputs. -/
def case1RowStrip_weightedPivotFirstSubstitutionData
    {ι κ τ R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (baseWeight : ι → R) (A : Matrix ι κ R)
    (C : Matrix (Unit ⊕ pivotComplement colPivot) τ R)
    (q : pivotComplement rowPivot → R)
    (hpivot : A rowPivot colPivot = 1)
    (hquot :
      ∀ i : pivotComplement rowPivot,
        u * baseWeight i.1 = q i * (u * baseWeight rowPivot)) :
    WeightedPivotFirstSubstitutionData
      R (pivotComplement rowPivot) (pivotComplement colPivot) τ where
  b0 := u * baseWeight rowPivot
  b := fun i ↦ u * baseWeight i.1
  q := q
  x := pivotFirstX rowPivot colPivot A
  y := pivotFirstY rowPivot colPivot A
  D := pivotFirstD rowPivot colPivot A
  weightedSource :=
    (diagonal (case1RowStripOldWeight strip u baseWeight) *
        case1RowStripSourceMatrix strip u A).submatrix
      (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)
  C := C
  source_eq := by
    rw [case1RowStrip_diagonal_mul_sourceMatrix_pivotFirst]
    rw [pivotFirstMatrix_eq_pivotPreQBlock A hpivot]
  quotient := hquot

/-- Case 1(2) displayed row-strip source-order `Q/P` identity from the
elementary row-strip weighting algebra and supplied quotient witnesses.  The
selected variable is counted once in the post row weights. -/
theorem case1RowStrip_sourceOrder_identity
    {ι κ τ R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (baseWeight : ι → R) (A : Matrix ι κ R)
    (C : Matrix (Unit ⊕ pivotComplement colPivot) τ R)
    (q : pivotComplement rowPivot → R)
    (hpivot : A rowPivot colPivot = 1)
    (hquot :
      ∀ i : pivotComplement rowPivot,
        u * baseWeight i.1 = q i * (u * baseWeight rowPivot)) :
    (weightedPivotBlockRowOp q
          (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
        (diagonal (case1RowStripOldWeight strip u baseWeight) *
          case1RowStripSourceMatrix strip u A).submatrix
          (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)) *
        C =
      (weightedPivotDiagonal
          (u * baseWeight rowPivot)
          (fun i : pivotComplement rowPivot ↦ u * baseWeight i.1) *
        weightedPivotClearedBlock
          (pivotFirstD rowPivot colPivot A -
            pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A)) *
        (pivotQinv (pivotFirstY rowPivot colPivot A) * C) :=
  WeightedPivotFirstSubstitutionData.sourceOrder_identity
    (case1RowStrip_weightedPivotFirstSubstitutionData
      strip u baseWeight A C q hpivot hquot)

/-- Displayed Case 1(2) row-strip pivot quotients for monomial-recursive row
weights.  This is only the divisibility needed by the displayed top-left `P`
matrix; it does not derive the recurrence data from a chart transition. -/
theorem exists_case1DisplayedRowStripPivot_quotients_of_rowIndex_monomialRec
    (step : ℕ → R) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      ∀ i,
        monomialRec step (case2ResidualRowLevel n S J i.1) =
          q i * monomialRec step
            (case2ResidualRowLevel n S J (case2DisplayedPivotRow n hS hcont)) := by
  rcases exists_right_quotients_monomialRec_of_le
      (step := step) (a := J + 1)
      (level := fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        case2ResidualRowLevel n S J i.1)
      (fun i ↦ case2ResidualRowLevel_ge n S J i.1) with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  intro i
  simpa [case2ResidualRowLevel_displayedPivotRow] using hq i

/-- Displayed Case 1(2) row-strip pivot quotients after common multiplication
by the selected variable.  The selected variable remains on both sides, so the
proof uses divisibility witnesses rather than cancellation or inverses. -/
theorem exists_case1DisplayedRowStripPivot_pivotMul_quotients_of_rowIndex_monomialRec
    (step : ℕ → R) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1)) (u : R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      ∀ i,
        u * monomialRec step (case2ResidualRowLevel n S J i.1) =
          q i * (u * monomialRec step
            (case2ResidualRowLevel n S J (case2DisplayedPivotRow n hS hcont))) := by
  rcases exists_right_quotients_pivotMul_monomialRec_of_le
      (step := step) u (a := J + 1)
      (level := fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        case2ResidualRowLevel n S J i.1)
      (fun i ↦ case2ResidualRowLevel_ge n S J i.1) with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  intro i
  simpa [case2ResidualRowLevel_displayedPivotRow] using hq i

/-- Packaged recurrence-state form of the displayed Case 1(2) row-strip pivot
quotients.  The state supplies the recurrence weights; no chart production or
post-transition data is asserted. -/
theorem exists_case1DisplayedRowStripPivot_pivotMul_quotients_of_recurrenceState
    (L : ℕ) {n : ℕ → ℕ} {S J : ℕ}
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (state : IntroducedLabelRecurrenceState L n S J R) (u : R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      ∀ i,
        u * state.case2ResidualRowWeight i.1 =
          q i * (u * state.case2ResidualRowWeight
            (case2DisplayedPivotRow n hS hcont)) := by
  rcases exists_case1DisplayedRowStripPivot_pivotMul_quotients_of_rowIndex_monomialRec
      state.step n hS hcont u with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  intro i
  simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight,
    IntroducedLabelRecurrenceState.weight] using hq i

/-- Displayed Case 1(2) row-strip source-order identity with quotient
witnesses chosen from row-indexed monomial recurrence weights.  The normalised
matrix, strip predicate, old-variable factorisation convention, and following
factor are still supplied. -/
theorem exists_case1RowStrip_sourceOrder_identity_of_rowIndex_monomialRec
    {ι κ τ R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {rowPivot : ι} {colPivot : κ}
    [Fintype (pivotComplement rowPivot)]
    [Fintype (pivotComplement colPivot)]
    (strip : ι → Prop) [DecidablePred strip] (u : R)
    (step : ℕ → R) (rowLevel : ι → ℕ) (pivotLevel : ℕ)
    (A : Matrix ι κ R)
    (C : Matrix (Unit ⊕ pivotComplement colPivot) τ R)
    (hpivot : A rowPivot colPivot = 1)
    (hpivotLevel : rowLevel rowPivot = pivotLevel)
    (hlevel : ∀ i : pivotComplement rowPivot, pivotLevel ≤ rowLevel i.1) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q
            (fun i ↦ pivotFirstX rowPivot colPivot A i ()) *
          (diagonal
              (case1RowStripOldWeight strip u
                (fun i ↦ monomialRec step (rowLevel i))) *
            case1RowStripSourceMatrix strip u A).submatrix
            (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)) *
          C =
        (weightedPivotDiagonal
            (u * monomialRec step (rowLevel rowPivot))
            (fun i : pivotComplement rowPivot ↦
              u * monomialRec step (rowLevel i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot A -
              pivotFirstX rowPivot colPivot A * pivotFirstY rowPivot colPivot A)) *
          (pivotQinv (pivotFirstY rowPivot colPivot A) * C) := by
  rcases exists_right_quotients_pivotMul_monomialRec_of_le
      (step := step) u (a := pivotLevel)
      (level := fun i : pivotComplement rowPivot ↦ rowLevel i.1)
      hlevel with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  refine case1RowStrip_sourceOrder_identity strip u
    (fun i ↦ monomialRec step (rowLevel i)) A C q hpivot ?_
  intro i
  change u * monomialRec step (rowLevel i.1) =
    q i * (u * monomialRec step (rowLevel rowPivot))
  rw [hpivotLevel]
  exact hq i

/-- Displayed Case 1(2) source-order identity for the top-left residual pivot,
with quotient witnesses chosen from the residual row index recurrence.  This is
finite source-order algebra only, not a Case 1 transition theorem. -/
theorem exists_case1DisplayedRowStrip_sourceOrder_identity_of_rowIndex_monomialRec
    {τ R : Type*} [CommRing R]
    (step : ℕ → R) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (strip : Case2ResidualRowIndex n S J → Prop) [DecidablePred strip] (u : R)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R)
    (C : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (hpivot :
      A (case2DisplayedPivotRow n hS hcont) (case2DisplayedPivotCol n hS hcont) = 1) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont) A i ()) *
          (diagonal
              (case1RowStripOldWeight strip u
                (fun i ↦ monomialRec step (case2ResidualRowLevel n S J i))) *
            case1RowStripSourceMatrix strip u A).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          C =
        (weightedPivotDiagonal
            (u * monomialRec step (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * monomialRec step (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont) A -
              pivotFirstX
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont) A *
                pivotFirstY
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont) A)) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont) A) * C) := by
  rcases exists_case1RowStrip_sourceOrder_identity_of_rowIndex_monomialRec
      strip u step (case2ResidualRowLevel n S J) (J + 1) A C hpivot
      (case2ResidualRowLevel_displayedPivotRow n hS hcont)
      (fun i ↦ case2ResidualRowLevel_ge n S J i.1) with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  simpa [case2ResidualRowLevel_displayedPivotRow] using hq

/-- Case 1(2) recurrence post-data boundary from a factored-old base state.

The `factoredBase` state is not the original pre-chart state: its selected old
variable has already been replaced by the residual old variable.  The supplied
post-data then adds the fresh label `(S,J+1)` at level `J` with variable `u`.
This is a naming boundary only, not a chart-production theorem. -/
abbrev Case1DisplayedRowStripFactoredBasePostData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {R : Type*}
    (factoredBase : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (u : R) : Prop :=
  IntroducedLabelRecurrenceState.Case2SuppliedPostData factoredBase post u

namespace IntroducedLabelRecurrenceState.Case2SuppliedPostData

/-- Displayed Case 1(2) row-strip source weights, transported from the
factored-old base recurrence to the supplied post recurrence weights.

The left side uses `case1RowStripOldWeight`, encoding that the selected old
variable has already been factored.  The right side uses the post-state
recurrence weights obtained by adding `(S,J+1)` at level `J`.  This is finite
recurrence/source-order algebra only; it does not relate the factored base
state to the original pre-chart state or prove that a chart produces the
post-state. -/
theorem case1DisplayedRowStrip_diagonal_mul_sourceMatrix_pivotFirst_succWeights
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {R : Type*} [CommRing R]
    {factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : Case1DisplayedRowStripFactoredBasePostData factoredBase post u)
    (hnew : actualWidthLabel L n S (J + 1))
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (strip : Case2ResidualRowIndex n S J → Prop) [DecidablePred strip]
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R) :
    (diagonal
        (case1RowStripOldWeight strip u
          (fun i ↦ factoredBase.case2ResidualRowWeight i)) *
      case1RowStripSourceMatrix strip u A).submatrix
        (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
        (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont)) =
      weightedPivotDiagonal
        (post.weight (J + 1))
        (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          post.weight (case2ResidualRowLevel n S J i.1)) *
        pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          A := by
  rw [case1RowStrip_diagonal_mul_sourceMatrix_pivotFirst]
  have hpivot :
      u * factoredBase.case2ResidualRowWeight (case2DisplayedPivotRow n hS hcont) =
        post.weight (J + 1) := by
    simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight,
      case2ResidualRowLevel_displayedPivotRow] using
      (hpost.weight_succ_current_eq_new_mul_of_ge (i := J + 1) hnew le_rfl).symm
  have hrows :
      (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          u * factoredBase.case2ResidualRowWeight i.1) =
        fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          post.weight (case2ResidualRowLevel n S J i.1) := by
    funext i
    exact (by
      simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight] using
        (hpost.weight_succ_current_eq_new_mul_of_ge hnew
          (case2ResidualRowLevel_ge n S J i.1)).symm)
  rw [hpivot, hrows]

/-- Displayed Case 1(2) source-order `Q/P` identity with supplied post
recurrence weights, relative to a factored-old base recurrence.

The quotient witnesses are still chosen from monomial divisibility in the
factored base recurrence.  The conclusion rewrites the common `u`-multiple
row weights as the supplied post-state weights. -/
theorem exists_case1DisplayedRowStrip_sourceOrder_identity_succWeights_of_postData
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : Case1DisplayedRowStripFactoredBasePostData factoredBase post u)
    (hnew : actualWidthLabel L n S (J + 1))
    (strip : Case2ResidualRowIndex n S J → Prop) [DecidablePred strip]
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R)
    (C : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (hpivot :
      A (case2DisplayedPivotRow n hS hcont) (case2DisplayedPivotCol n hS hcont) = 1) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont) A i ()) *
          (diagonal
              (case1RowStripOldWeight strip u
                (fun i ↦ factoredBase.case2ResidualRowWeight i)) *
            case1RowStripSourceMatrix strip u A).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont) A -
              pivotFirstX
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont) A *
                pivotFirstY
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont) A)) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont) A) * C) := by
  rcases exists_case1DisplayedRowStrip_sourceOrder_identity_of_rowIndex_monomialRec
      factoredBase.step n hS hcont strip u A C hpivot with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hpivotWeight :
      u * monomialRec factoredBase.step (J + 1) = post.weight (J + 1) := by
    simpa [IntroducedLabelRecurrenceState.weight] using
      (hpost.weight_succ_current_eq_new_mul_of_ge (i := J + 1) hnew le_rfl).symm
  have hrowWeights :
      (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          u * monomialRec factoredBase.step (case2ResidualRowLevel n S J i.1)) =
        fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          post.weight (case2ResidualRowLevel n S J i.1) := by
    funext i
    exact (by
      simpa [IntroducedLabelRecurrenceState.weight] using
        (hpost.weight_succ_current_eq_new_mul_of_ge hnew
          (case2ResidualRowLevel_ge n S J i.1)).symm)
  rw [hpivotWeight, hrowWeights] at hq
  simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight,
    IntroducedLabelRecurrenceState.weight] using hq

/-- Displayed Case 1(2) source-order `Q/P` identity with the original source
recurrence convention on the left and supplied post recurrence weights on the
right.

The left diagonal keeps the old selected factor at its source level `J+J1`;
the row-strip matrix divides exactly the rows `J+1..J+J1`.  The right diagonal
uses the supplied post-state weights after adding the fresh label `(S,J+1)` at
level `J`.  This combines the source-weight boundary and the factored-base
post-data boundary, but still does not construct the factored base or prove
chart production. -/
theorem exists_case1DisplayedRowStrip_sourceOrder_identity_sourceWeights_succWeights_of_postData
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 : ℕ}
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : Case1DisplayedRowStripFactoredBasePostData factoredBase post u)
    (hnew : actualWidthLabel L n S (J + 1))
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R)
    (C : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (hpivot :
      A (case2DisplayedPivotRow n hS hcont) (case2DisplayedPivotCol n hS hcont) = 1) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont) A i ()) *
          (diagonal
              (fun i ↦
                monomialRec (mulStepAt factoredBase.step u (J + J1))
                  (case2ResidualRowLevel n S J i)) *
            case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n hS hcont)
                (case2DisplayedPivotCol n hS hcont) A -
              pivotFirstX
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont) A *
                pivotFirstY
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont) A)) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont) A) * C) := by
  rcases hpost.exists_case1DisplayedRowStrip_sourceOrder_identity_succWeights_of_postData
      hS hcont hnew (case1ResidualRowStrip n S J J1) A C hpivot with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hweights :
      case1RowStripOldWeight (case1ResidualRowStrip n S J J1) u
          (fun i ↦ factoredBase.case2ResidualRowWeight i) =
        fun i ↦
          monomialRec (mulStepAt factoredBase.step u (J + J1))
            (case2ResidualRowLevel n S J i) := by
    simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight,
      IntroducedLabelRecurrenceState.weight] using
      case1ResidualRowStripOldWeight_eq_sourceMulStepAt
        factoredBase.step u n S J J1
  rwa [hweights] at hq

end IntroducedLabelRecurrenceState.Case2SuppliedPostData

/-- Supplied transition boundary for Aoyagi's displayed Case 1(2) row-strip
pivot.

This packages only the data that has already been separated into elementary
boundaries:

* first-jump arithmetic for the selected old label;
* actual source bounds for the fresh label `(S,J+1)`;
* supplied recurrence post-data relative to a factored-old base state;
* supplied pre-state exponent certificates and level-tail invariants;
* supplied exponent post-data for the fresh label.

It deliberately does not construct the factored-base state from the original
pre-chart state, prove hidden old-label validity, construct a chart, prove
coverage, compute a Jacobian, or assert a transition invariant. -/
structure Case1DisplayedRowStripSuppliedTransitionBoundary
    (R : Type*) (L : ℕ) (n : ℕ → ℕ) (S J J1 s0 k0 : ℕ)
    (level : ℕ → ℕ → ℕ)
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ)
    (factoredBase : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (u : R) : Prop where
  firstJump : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t
  stage_ge_two : 2 ≤ S
  stage_le : S ≤ L
  source_col_bound : J + 1 ≤ n (S + 1)
  exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue
  levelTail : IntroducedLabelLevelTailInvariants L n S J level t leastValue
  recurrencePost : Case1DisplayedRowStripFactoredBasePostData factoredBase post u
  exponentPost :
    Case1DisplayedRowStripExponentPostData
      (L := L) (n := n) (S := S) (J := J) (J1 := J1) (s0 := s0) (k0 := k0)
      t t' numerator numerator' leastValue leastValue'

namespace Case1DisplayedRowStripSuppliedTransitionBoundary

theorem stage_pos
    {R : Type*} {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSuppliedTransitionBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue' factoredBase post u) :
    1 ≤ S := by
  exact le_trans (by omega : 1 ≤ 2) data.stage_ge_two

/-- The first-jump row bound and actual source column bound give the displayed
top-left continuation bound used by the residual pivot indices. -/
theorem continuationBound
    {R : Type*} {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSuppliedTransitionBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue' factoredBase post u) :
    J + 1 ≤ prefixMinNat n (S + 1) :=
  data.firstJump.continuationBound_of_colBound data.stage_pos data.source_col_bound

/-- The same source column bound gives actual-width validity of the fresh
post-state label `(S,J+1)`. -/
theorem newLabelActualWidth
    {R : Type*} {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSuppliedTransitionBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue' factoredBase post u) :
    actualWidthLabel L n S (J + 1) :=
  actualWidthLabel_case2_new L n data.stage_pos data.stage_le data.source_col_bound

/-- The displayed top-left Case 1(2) source-order identity available from the
supplied transition boundary.

The left diagonal is the original source recurrence with the old selected
factor still at level `J+J1`; the right diagonal is the supplied post
recurrence after the new label `(S,J+1)` has been inserted at level `J`. -/
theorem sourceOrder_identity_sourceWeights
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSuppliedTransitionBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue' factoredBase post u)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R)
    (C :
      Matrix
        (Unit ⊕ pivotComplement
          (case2DisplayedPivotCol n data.stage_pos data.continuationBound)) τ R)
    (hpivot :
      A (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
        (case2DisplayedPivotCol n data.stage_pos data.continuationBound) = 1) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n data.stage_pos data.continuationBound) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
                (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A i ()) *
          (diagonal
              (fun i ↦
                monomialRec (mulStepAt factoredBase.step u (J + J1))
                  (case2ResidualRowLevel n S J i)) *
            case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A).submatrix
            (pivotFirstIndexEquiv
              (case2DisplayedPivotRow n data.stage_pos data.continuationBound))
            (pivotFirstIndexEquiv
              (case2DisplayedPivotCol n data.stage_pos data.continuationBound))) *
          C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i :
                pivotComplement
                  (case2DisplayedPivotRow n data.stage_pos data.continuationBound) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
                (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A -
              pivotFirstX
                  (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
                  (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A *
                pivotFirstY
                  (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
                  (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A)) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
              (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A) * C) :=
  data.recurrencePost
    |>.exists_case1DisplayedRowStrip_sourceOrder_identity_sourceWeights_succWeights_of_postData
      data.stage_pos data.continuationBound data.newLabelActualWidth A C hpivot

/-- Source-facing displayed top-left Case 1(2) source-order identity.

This rewrites the local handoff's left diagonal from the explicit
`mulStepAt factoredBase.step u (J+J1)` recurrence into the supplied substituted
source recurrence weights.  The `source` state is still supplied and is
assumed to be the pullback after `old = u * old'`; this theorem does not
construct that pullback or the selected-old chart. -/
theorem sourceOrder_identity_substitutedSourceWeights
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSuppliedTransitionBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue' factoredBase post u)
    (hsource :
      IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData
        source factoredBase s0 k0 u)
    (hlevel : level = factoredBase.level)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R)
    (C :
      Matrix
        (Unit ⊕ pivotComplement
          (case2DisplayedPivotCol n data.stage_pos data.continuationBound)) τ R)
    (hpivot :
      A (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
        (case2DisplayedPivotCol n data.stage_pos data.continuationBound) = 1) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n data.stage_pos data.continuationBound) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
                (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A i ()) *
          (diagonal
              (fun i ↦ source.weight (case2ResidualRowLevel n S J i)) *
            case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A).submatrix
            (pivotFirstIndexEquiv
              (case2DisplayedPivotRow n data.stage_pos data.continuationBound))
            (pivotFirstIndexEquiv
              (case2DisplayedPivotCol n data.stage_pos data.continuationBound))) *
          C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i :
                pivotComplement
                  (case2DisplayedPivotRow n data.stage_pos data.continuationBound) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
                (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A -
              pivotFirstX
                  (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
                  (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A *
                pivotFirstY
                  (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
                  (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A)) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n data.stage_pos data.continuationBound)
              (case2DisplayedPivotCol n data.stage_pos data.continuationBound) A) * C) := by
  rcases data.sourceOrder_identity_sourceWeights A C hpivot with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hfirst :
      Case1FirstJumpHypotheses L n S J J1 s0 k0 factoredBase.level t := by
    simpa [hlevel] using data.firstJump
  have hstep := hsource.step_eq_mulStepAt_of_firstJump hfirst
  have hweights :
      (fun i : Case2ResidualRowIndex n S J ↦
          monomialRec (mulStepAt factoredBase.step u (J + J1))
            (case2ResidualRowLevel n S J i)) =
        fun i ↦ source.weight (case2ResidualRowLevel n S J i) := by
    funext i
    rw [← hstep]
    rfl
  rwa [hweights] at hq

/-- The supplied exponent post-data extends the introduced-label exponent
certificate domain by the fresh Case 1(2) displayed row-strip label. -/
theorem extendExponentDomain
    {R : Type*} {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSuppliedTransitionBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue' factoredBase post u) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' :=
  data.exponentPre.extendDomain_case1DisplayedRowStripNewLabel_of_postData data.firstJump
    (data.levelTail.leastValue_eq_level data.firstJump.selectedIntroduced)
    (data.levelTail.flatTail_abovePivot data.firstJump.selectedIntroduced
      data.firstJump.lt_selectedLevel)
    data.stage_ge_two data.stage_le data.source_col_bound data.exponentPost

end Case1DisplayedRowStripSuppliedTransitionBoundary

/-- Source-facing supplied boundary for Aoyagi's displayed Case 1(2)
selected-old pullback.

The local row-strip handoff is specialized to `factoredBase.level`, so using
the selected old-label source pullback no longer needs a separate level-map
identification.  This remains an assumption interface: it records the
selected-old pullback and the supplied local handoff, but does not construct
the selected-old chart, identify the `Unit` center generator with `(s0,k0)` by
itself, prove coverage, compute Jacobians, or assert normal crossings/RLCT. -/
structure Case1DisplayedRowStripSelectedOldPullbackBoundary
    (R : Type*) [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J J1 s0 k0 : ℕ)
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ)
    (source factoredBase : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (u : R) : Prop where
  handoff :
    Case1DisplayedRowStripSuppliedTransitionBoundary R L n S J J1 s0 k0
      factoredBase.level
      t t' numerator numerator' leastValue leastValue' factoredBase post u
  sourcePullback :
    IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData
      source factoredBase s0 k0 u

namespace Case1DisplayedRowStripSelectedOldPullbackBoundary

/-- The bundled local handoff supplies first-jump data on the recurrence-state
level map of the factored-base state. -/
theorem factoredBaseFirstJump
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
        t t' numerator numerator' leastValue leastValue'
        source factoredBase post u) :
    Case1FirstJumpHypotheses L n S J J1 s0 k0 factoredBase.level t :=
  data.handoff.firstJump

/-- The `Unit` branch is the selected old center-generator token.  This is
finite-center membership only; the source label `(s0,k0)` is supplied
separately by `sourcePullback` and `factoredBaseFirstJump`. -/
theorem selectedOld_mem_center
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (_data :
      Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
        t t' numerator numerator' leastValue leastValue'
        source factoredBase post u) :
    (Sum.inl () : Case1CenterGenerator) ∈ case1CenterGenerators n S J J1 :=
  case1_selectedOld_mem_center n S J J1

/-- The selected old source label is supplied as an introduced label in the
pullback recurrence data. -/
theorem sourcePullback_selectedIntroduced
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
        t t' numerator numerator' leastValue leastValue'
        source factoredBase post u) :
    introducedLabel L n S J s0 k0 :=
  data.sourcePullback.selectedIntroduced

/-- The selected old source label has level `J+J1` in the factored-base
recurrence-state level map. -/
theorem selectedLevel
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
        t t' numerator numerator' leastValue leastValue'
        source factoredBase post u) :
    factoredBase.level s0 k0 = J + J1 :=
  data.factoredBaseFirstJump.selectedLevel

/-- The supplied selected-old pullback changes the source recurrence by
inserting one factor `u` at the selected old level `J+J1`. -/
theorem source_step_eq_mulStepAt
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
        t t' numerator numerator' leastValue leastValue'
        source factoredBase post u) :
    source.step = mulStepAt factoredBase.step u (J + J1) :=
  data.sourcePullback.step_eq_mulStepAt_of_firstJump data.factoredBaseFirstJump

/-- The row-strip old-weight convention is exactly the supplied source
pullback recurrence weights. -/
theorem residualRowStripOldWeight_eq_sourceWeight
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
        t t' numerator numerator' leastValue leastValue'
        source factoredBase post u) :
    case1RowStripOldWeight (case1ResidualRowStrip n S J J1) u
        (fun i ↦ factoredBase.case2ResidualRowWeight i) =
      fun i ↦ source.weight (case2ResidualRowLevel n S J i) :=
  case1ResidualRowStripOldWeight_eq_sourceWeight_of_selectedOldFactoredBase
    data.sourcePullback data.factoredBaseFirstJump

/-- The source-facing displayed Case 1(2) source-order identity, with the left
diagonal already written in the supplied source-pullback weights. -/
theorem sourceOrder_identity
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
        t t' numerator numerator' leastValue leastValue'
        source factoredBase post u)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R)
    (C :
      Matrix
        (Unit ⊕ pivotComplement
          (case2DisplayedPivotCol n data.handoff.stage_pos
            data.handoff.continuationBound)) τ R)
    (hpivot :
      A (case2DisplayedPivotRow n data.handoff.stage_pos data.handoff.continuationBound)
        (case2DisplayedPivotCol n data.handoff.stage_pos
          data.handoff.continuationBound) = 1) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.handoff.stage_pos data.handoff.continuationBound) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n data.handoff.stage_pos data.handoff.continuationBound)
                (case2DisplayedPivotCol n data.handoff.stage_pos
                  data.handoff.continuationBound)
                A i ()) *
          (diagonal
              (fun i ↦ source.weight (case2ResidualRowLevel n S J i)) *
            case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A).submatrix
            (pivotFirstIndexEquiv
              (case2DisplayedPivotRow n data.handoff.stage_pos
                data.handoff.continuationBound))
            (pivotFirstIndexEquiv
              (case2DisplayedPivotCol n data.handoff.stage_pos
                data.handoff.continuationBound))) *
          C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i :
                pivotComplement
                  (case2DisplayedPivotRow n data.handoff.stage_pos
                    data.handoff.continuationBound) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n data.handoff.stage_pos data.handoff.continuationBound)
                (case2DisplayedPivotCol n data.handoff.stage_pos
                  data.handoff.continuationBound)
                A -
              pivotFirstX
                  (case2DisplayedPivotRow n data.handoff.stage_pos
                    data.handoff.continuationBound)
                  (case2DisplayedPivotCol n data.handoff.stage_pos
                    data.handoff.continuationBound)
                  A *
                pivotFirstY
                  (case2DisplayedPivotRow n data.handoff.stage_pos
                    data.handoff.continuationBound)
                  (case2DisplayedPivotCol n data.handoff.stage_pos
                    data.handoff.continuationBound)
                  A)) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n data.handoff.stage_pos data.handoff.continuationBound)
              (case2DisplayedPivotCol n data.handoff.stage_pos
                data.handoff.continuationBound)
              A) * C) :=
  data.handoff.sourceOrder_identity_substitutedSourceWeights data.sourcePullback rfl A C hpivot

/-- The bundled local handoff extends the exponent certificate domain by the
fresh Case 1(2) displayed row-strip label. -/
theorem extendExponentDomain
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (data :
      Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
        t t' numerator numerator' leastValue leastValue'
        source factoredBase post u) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' :=
  data.handoff.extendExponentDomain

end Case1DisplayedRowStripSelectedOldPullbackBoundary

/-- Supplied chart-family boundary for Aoyagi's displayed Case 1(2)
selected-old pullback.

This combines the source-facing selected-old pullback/local handoff boundary
with an explicitly supplied Case 1 finite chart-family regularity boundary.
It is still not chart production: regularity and transition regularity are
fields, not theorems constructed from coordinates. -/
structure Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary
    (R : Type*) [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J J1 s0 k0 : ℕ)
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ)
    (source factoredBase : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (u : R)
    (ChartRegular : Case1CenterGenerator → Prop)
    (TransitionRegular :
      Case1CenterGenerator → Case1CenterGenerator → Prop) : Prop where
  pullback :
    Case1DisplayedRowStripSelectedOldPullbackBoundary R L n S J J1 s0 k0
      t t' numerator numerator' leastValue leastValue'
      source factoredBase post u
  chartFamily :
    Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular

namespace Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary

/-- The supplied boundary still records the chosen old source label as an
introduced label through the pullback data, not through the `Unit` token alone. -/
theorem sourcePullback_selectedIntroduced
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    introducedLabel L n S J s0 k0 :=
  data.pullback.sourcePullback_selectedIntroduced

/-- The selected old source label has level `J+J1`; this is supplied by the
pullback/local handoff boundary. -/
theorem selectedLevel
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    factoredBase.level s0 k0 = J + J1 :=
  data.pullback.selectedLevel

/-- The selected old `Unit` token is in the supplied finite Case 1 center. -/
theorem selectedOld_mem_center
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    (Sum.inl () : Case1CenterGenerator) ∈ case1CenterGenerators n S J J1 :=
  data.pullback.selectedOld_mem_center

/-- The displayed top-left row-strip pivot is in the supplied finite Case 1
center, using first-jump positivity and the source column bound. -/
theorem displayedPivot_mem_center
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) ∈
      case1CenterGenerators n S J J1 :=
  data.pullback.factoredBaseFirstJump.displayedPivot_mem_center_of_colBound
    data.pullback.handoff.source_col_bound

/-- Supplied chart-family regularity for the selected old chart token. -/
theorem chart_regular_selectedOld
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    ChartRegular (Sum.inl () : Case1CenterGenerator) :=
  Case1CenterChartFamilyBoundary.chart_regular_of_mem data.chartFamily
    data.selectedOld_mem_center

/-- Supplied chart-family regularity for Aoyagi's displayed top-left
row-strip chart. -/
theorem chart_regular_displayedPivot
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    ChartRegular (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) :=
  Case1CenterChartFamilyBoundary.chart_regular_of_mem data.chartFamily
    data.displayedPivot_mem_center

/-- Supplied transition regularity from the selected old chart token to the
displayed top-left row-strip chart. -/
theorem transition_regular_selectedOld_displayedPivot
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    TransitionRegular
      (Sum.inl () : Case1CenterGenerator)
      (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) :=
  Case1CenterChartFamilyBoundary.transition_regular_of_mem data.chartFamily
    data.selectedOld_mem_center data.displayedPivot_mem_center

/-- Supplied transition regularity from the displayed top-left row-strip chart
back to the selected old chart token. -/
theorem transition_regular_displayedPivot_selectedOld
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    TransitionRegular
      (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)
      (Sum.inl () : Case1CenterGenerator) :=
  Case1CenterChartFamilyBoundary.transition_regular_of_mem data.chartFamily
    data.displayedPivot_mem_center data.selectedOld_mem_center

/-- In the displayed top-left row-strip chart, the selected variable occurs as
a value of the transformed finite Case 1 center. -/
theorem displayedPivot_selectedEntryChartMap_value_mem
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular)
    (residual : Case1CenterGenerator → R) :
    u ∈
      {v : R | ∃ g, g ∈ case1CenterGenerators n S J J1 ∧
        selectedEntryChartMap (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)
          u residual g = v} :=
  selectedEntryChartMap_pivot_mem_valueSet data.displayedPivot_mem_center u residual

/-- In the displayed top-left row-strip chart, every transformed finite Case 1
center generator is divisible by the selected variable. -/
theorem displayedPivot_center_dvd
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular)
    (residual : Case1CenterGenerator → R) :
    ∀ g, g ∈ case1CenterGenerators n S J J1 →
      u ∣ selectedEntryChartMap
        (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) u residual g :=
  case1_selectedEntryChartMap_center_dvd_of_mem data.displayedPivot_mem_center u residual

/-- In the displayed top-left row-strip chart, the transformed finite Case 1
center ideal is the principal ideal generated by the selected variable. -/
theorem displayedPivot_centerIdeal_eq_span_singleton
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular)
    (residual : Case1CenterGenerator → R) :
    Ideal.span
        {v : R | ∃ g, g ∈ case1CenterGenerators n S J J1 ∧
          selectedEntryChartMap (Sum.inr (J + 1, J + 1) : Case1CenterGenerator)
            u residual g = v} =
      Ideal.span ({u} : Set R) :=
  case1_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem
    data.displayedPivot_mem_center u residual

/-- The supplied selected-old pullback still gives the recurrence update at
the old selected level. -/
theorem source_step_eq_mulStepAt
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    source.step = mulStepAt factoredBase.step u (J + J1) :=
  data.pullback.source_step_eq_mulStepAt

/-- The supplied chart-family boundary keeps the source-facing Case 1(2)
source-order identity from the selected-old pullback boundary. -/
theorem sourceOrder_identity
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R)
    (C :
      Matrix
        (Unit ⊕ pivotComplement
          (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
            data.pullback.handoff.continuationBound)) τ R)
    (hpivot :
      A (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
          data.pullback.handoff.continuationBound)
        (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
          data.pullback.handoff.continuationBound) = 1) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
          data.pullback.handoff.continuationBound) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                A i ()) *
          (diagonal
              (fun i ↦ source.weight (case2ResidualRowLevel n S J i)) *
            case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A).submatrix
            (pivotFirstIndexEquiv
              (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound))
            (pivotFirstIndexEquiv
              (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound))) *
          C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i :
                pivotComplement
                  (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                A -
              pivotFirstX
                  (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound)
                  (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound)
                  A *
                pivotFirstY
                  (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound)
                  (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound)
                  A)) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound)
              (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound)
              A) * C) :=
  data.pullback.sourceOrder_identity A C hpivot

/-- The supplied chart-family boundary keeps the exponent-domain extension
from the selected-old pullback boundary. -/
theorem extendExponentDomain
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' :=
  data.pullback.extendExponentDomain

end Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary

/-- Supplied-data boundary for Aoyagi's displayed Case 1(2) row-strip pivot.
It combines the finite first-jump/source-validity facts with an already
supplied weighted pivot-first source block.  It does not construct the
selected-entry chart, encode the hidden old label, prove coverage, or produce
transition post-data. -/
structure Case1DisplayedRowStripSuppliedWeightedSourceData
    (R ρ κ τ : Type*) [CommRing R] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] [DecidableEq κ]
    (L : ℕ) (n : ℕ → ℕ) (S J J1 s k : ℕ)
    (level : ℕ → ℕ → ℕ) (vector : ℕ → ℕ → ℕ → ℤ) where
  firstJump : Case1FirstJumpHypotheses L n S J J1 s k level vector
  stage_pos : 1 ≤ S
  source_col_bound : J + 1 ≤ n (S + 1)
  weighted : WeightedPivotFirstSubstitutionData R ρ κ τ

namespace Case1DisplayedRowStripSuppliedWeightedSourceData

/-- The displayed Case 1(2) pivot satisfies the continuation bound once the
actual source column bound is supplied. -/
theorem continuationBound
    {R ρ κ τ : Type*} [CommRing R] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] [DecidableEq κ]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (data :
      Case1DisplayedRowStripSuppliedWeightedSourceData
        R ρ κ τ L n S J J1 s k level vector) :
    J + 1 ≤ prefixMinNat n (S + 1) :=
  data.firstJump.continuationBound_of_colBound data.stage_pos data.source_col_bound

/-- The displayed top-left strip entry belongs to the finite Case 1 center. -/
theorem displayedPivot_mem_center
    {R ρ κ τ : Type*} [CommRing R] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] [DecidableEq κ]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (data :
      Case1DisplayedRowStripSuppliedWeightedSourceData
        R ρ κ τ L n S J J1 s k level vector) :
    (Sum.inr (J + 1, J + 1) : Case1CenterGenerator) ∈
      case1CenterGenerators n S J J1 :=
  data.firstJump.displayedPivot_mem_center_of_colBound data.source_col_bound

/-- The displayed top-left strip entry is also a residual-block pivot entry
under the first-jump row bound and source column bound. -/
theorem displayedPivot_mem_residualBlockPivotEntries
    {R ρ κ τ : Type*} [CommRing R] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] [DecidableEq κ]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (data :
      Case1DisplayedRowStripSuppliedWeightedSourceData
        R ρ κ τ L n S J J1 s k level vector) :
    (J + 1, J + 1) ∈ case2ResidualBlockPivotEntries n S J :=
  data.firstJump.displayedPivot_mem_residualBlockPivotEntries_of_colBound
    data.source_col_bound

/-- The generic displayed top-left source-order identity applies to the
supplied Case 1(2) weighted pivot-first source block. -/
theorem sourceOrder_identity
    {R ρ κ τ : Type*} [CommRing R] [Fintype ρ] [DecidableEq ρ]
    [Fintype κ] [DecidableEq κ]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s k : ℕ}
    {level : ℕ → ℕ → ℕ} {vector : ℕ → ℕ → ℕ → ℤ}
    (data :
      Case1DisplayedRowStripSuppliedWeightedSourceData
        R ρ κ τ L n S J J1 s k level vector) :
    (weightedPivotBlockRowOp data.weighted.q
          (fun i ↦ data.weighted.x i ()) *
        data.weighted.weightedSource) *
        data.weighted.C =
      (weightedPivotDiagonal data.weighted.b0 data.weighted.b *
          weightedPivotClearedBlock
            (data.weighted.D - data.weighted.x * data.weighted.y)) *
        (pivotQinv data.weighted.y * data.weighted.C) :=
  WeightedPivotFirstSubstitutionData.sourceOrder_identity data.weighted

end Case1DisplayedRowStripSuppliedWeightedSourceData

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

/-- The normalised residual block for an arbitrary selected Case 2 pivot entry.
The pivot is a supplied residual-row/column subtype, so this is finite algebra
only, not chart coverage. -/
def case2SelectedNormalizedMatrix
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  selectedEntryNormalizedMatrix rowPivot colPivot residual

/-- The source-substituted residual block for an arbitrary selected Case 2
pivot entry. -/
def case2SelectedSubstitutionMatrix
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J) (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  selectedEntrySubstitutionMatrix rowPivot colPivot u residual

/-- The arbitrary selected Case 2 substituted block is `u` times the normalised
residual block. -/
theorem case2SelectedSubstitutionMatrix_eq_mul_normalized
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J) (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    case2SelectedSubstitutionMatrix rowPivot colPivot u residual =
      fun i j ↦ u * case2SelectedNormalizedMatrix rowPivot colPivot residual i j :=
  rfl

/-- Arbitrary Case 2 selected-entry source-variable transport: the selected
variable in the substituted residual block can be absorbed into pivot-first row
weights.  This is not chart coverage or source-displayed arbitrary-pivot data. -/
theorem case2Selected_diagonal_mul_substitutionMatrix_pivotFirst
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J) (u : R)
    (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    (diagonal weight * case2SelectedSubstitutionMatrix rowPivot colPivot u residual).submatrix
        (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot) =
      weightedPivotDiagonal
        (u * weight rowPivot)
        (fun i : pivotComplement rowPivot ↦ u * weight i.1) *
        pivotFirstMatrix rowPivot colPivot
          (case2SelectedNormalizedMatrix rowPivot colPivot residual) := by
  simpa [case2SelectedSubstitutionMatrix, case2SelectedNormalizedMatrix] using
    pivotFirst_diagonal_mul_selectedEntrySubstitutionMatrix
      (rowPivot := rowPivot) (colPivot := colPivot) u weight residual

/-- The following factor for an arbitrary selected Case 2 pivot, reindexed into
pivot-first column order. -/
def case2SelectedFollowingFactor
    {n : ℕ → ℕ} {S J : ℕ}
    (colPivot : Case2ResidualColIndex n S J)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    Matrix (Unit ⊕ pivotComplement colPivot) τ R :=
  pivotFirstFollowingFactor colPivot C

/-- The arbitrary selected Case 2 following factor after the corresponding
`Q⁻¹ C` update. -/
def case2SelectedTransportedFollowingFactor
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    Matrix (Unit ⊕ pivotComplement colPivot) τ R :=
  pivotQinv
      (pivotFirstY rowPivot colPivot
        (case2SelectedNormalizedMatrix rowPivot colPivot residual)) *
    case2SelectedFollowingFactor colPivot C

/-- Arbitrary selected Case 2 following-factor transport for the normalised
residual block. -/
theorem case2SelectedNormalizedMatrix_mul_followingFactor
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    pivotFirstMatrix rowPivot colPivot
        (case2SelectedNormalizedMatrix rowPivot colPivot residual) *
      case2SelectedFollowingFactor colPivot C =
    (case2SelectedNormalizedMatrix rowPivot colPivot residual * C).submatrix
      (pivotFirstIndexEquiv rowPivot) id := by
  exact pivotFirstMatrix_mul_pivotFirstFollowingFactor
    (case2SelectedNormalizedMatrix rowPivot colPivot residual) C

/-- Arbitrary selected Case 2 source-variable transport with the following
factor included. -/
theorem case2Selected_diagonal_mul_substitutionMatrix_mul_followingFactor
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J) (u : R)
    (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ((diagonal weight * case2SelectedSubstitutionMatrix rowPivot colPivot u residual) *
        C).submatrix (pivotFirstIndexEquiv rowPivot) id =
      (weightedPivotDiagonal
          (u * weight rowPivot)
          (fun i : pivotComplement rowPivot ↦ u * weight i.1) *
        pivotFirstMatrix rowPivot colPivot
          (case2SelectedNormalizedMatrix rowPivot colPivot residual)) *
        case2SelectedFollowingFactor colPivot C := by
  rw [← Matrix.submatrix_mul_equiv
    (diagonal weight * case2SelectedSubstitutionMatrix rowPivot colPivot u residual)
    C (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot) id]
  rw [case2Selected_diagonal_mul_substitutionMatrix_pivotFirst]
  rfl

/-- Arbitrary selected Case 2 `Q/P` source-substitution identity under explicit
divisibility of every pivot-complement row weight by the selected pivot-row
weight.  This is a conditional finite-algebra wrapper, not a proof of
arbitrary-pivot chart coverage. -/
theorem exists_case2SelectedQP_mul_sourceSubstitution_of_forall_dvd
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J) (u : R)
    (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R)
    (hdiv : ∀ i : pivotComplement rowPivot, u * weight rowPivot ∣ u * weight i.1) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX rowPivot colPivot
              (case2SelectedNormalizedMatrix rowPivot colPivot residual) i ()) *
          (diagonal weight *
            case2SelectedSubstitutionMatrix rowPivot colPivot u residual).submatrix
            (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)) *
          case2SelectedFollowingFactor colPivot C =
        (weightedPivotDiagonal
            (u * weight rowPivot)
            (fun i : pivotComplement rowPivot ↦ u * weight i.1) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot
                (case2SelectedNormalizedMatrix rowPivot colPivot residual) -
              pivotFirstX rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual) *
                pivotFirstY rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual))) *
          case2SelectedTransportedFollowingFactor rowPivot colPivot residual C := by
  have hpivot :
      case2SelectedNormalizedMatrix rowPivot colPivot residual rowPivot colPivot = 1 := by
    simp [case2SelectedNormalizedMatrix]
  rcases exists_pivotFirstQP_mul_of_forall_dvd
      (u * weight rowPivot)
      (fun i : pivotComplement rowPivot ↦ u * weight i.1)
      (case2SelectedNormalizedMatrix rowPivot colPivot residual)
      hpivot
      (case2SelectedFollowingFactor colPivot C)
      hdiv with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [case2Selected_diagonal_mul_substitutionMatrix_pivotFirst]
  rw [← Matrix.mul_assoc
    (weightedPivotBlockRowOp q
      (fun i ↦
        pivotFirstX rowPivot colPivot
          (case2SelectedNormalizedMatrix rowPivot colPivot residual) i ()))
    (weightedPivotDiagonal
      (u * weight rowPivot)
      (fun i : pivotComplement rowPivot ↦ u * weight i.1))
    (pivotFirstMatrix rowPivot colPivot
      (case2SelectedNormalizedMatrix rowPivot colPivot residual))]
  simpa [case2SelectedTransportedFollowingFactor] using hq

/-- Arbitrary selected Case 2 `Q/P` source-substitution identity under flat
residual-row weights. -/
theorem exists_case2SelectedQP_mul_sourceSubstitution_of_flat_weights
    {n : ℕ → ℕ} {S J : ℕ}
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J) (u : R)
    (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R)
    (hflat : ∀ i, weight i = weight rowPivot) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX rowPivot colPivot
              (case2SelectedNormalizedMatrix rowPivot colPivot residual) i ()) *
          (diagonal weight *
            case2SelectedSubstitutionMatrix rowPivot colPivot u residual).submatrix
            (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)) *
          case2SelectedFollowingFactor colPivot C =
        (weightedPivotDiagonal
            (u * weight rowPivot)
            (fun i : pivotComplement rowPivot ↦ u * weight i.1) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot
                (case2SelectedNormalizedMatrix rowPivot colPivot residual) -
              pivotFirstX rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual) *
                pivotFirstY rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual))) *
          case2SelectedTransportedFollowingFactor rowPivot colPivot residual C := by
  refine exists_case2SelectedQP_mul_sourceSubstitution_of_forall_dvd
    rowPivot colPivot u weight residual C ?_
  intro i
  rw [hflat i.1]

/-- Arbitrary selected Case 2 source-substitution `Q/P` identity for a packaged
introduced-label recurrence state satisfying the Case 2 gap. -/
theorem exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap
    (L : ℕ) {n : ℕ → ℕ} {S J : ℕ}
    (state : IntroducedLabelRecurrenceState L n S J R)
    (hgap : state.case2Gap)
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J) (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX rowPivot colPivot
              (case2SelectedNormalizedMatrix rowPivot colPivot residual) i ()) *
          (diagonal (fun i ↦ state.case2ResidualRowWeight i) *
            case2SelectedSubstitutionMatrix rowPivot colPivot u residual).submatrix
            (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)) *
          case2SelectedFollowingFactor colPivot C =
        (weightedPivotDiagonal
            (u * state.case2ResidualRowWeight rowPivot)
            (fun i : pivotComplement rowPivot ↦ u * state.case2ResidualRowWeight i.1) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot
                (case2SelectedNormalizedMatrix rowPivot colPivot residual) -
              pivotFirstX rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual) *
                pivotFirstY rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual))) *
          case2SelectedTransportedFollowingFactor rowPivot colPivot residual C := by
  refine exists_case2SelectedQP_mul_sourceSubstitution_of_flat_weights
    rowPivot colPivot u (fun i ↦ state.case2ResidualRowWeight i) residual C ?_
  intro i
  change state.case2ResidualRowWeight i = state.case2ResidualRowWeight rowPivot
  rw [state.case2ResidualRowWeight_eq_pivot_of_case2Gap hgap i,
    state.case2ResidualRowWeight_eq_pivot_of_case2Gap hgap rowPivot]

namespace CorrectedCase2NewLabelCertificate

/-- Arbitrary selected Case 2 source-variable transport with supplied successor
recurrence weights.  The source-substituted block is still formed with old row
weights; the selected variable has been absorbed into the supplied post-state
weights on the old residual rows. -/
theorem case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (u : R)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → post.level s k = pre.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → post.var s k = pre.var s k)
    (hlevel_new : post.level S (J + 1) = J)
    (hvar_new : post.var S (J + 1) = u)
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
        case2SelectedSubstitutionMatrix rowPivot colPivot u residual).submatrix
        (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot) =
      weightedPivotDiagonal
        (post.weight (case2ResidualRowLevel n S J rowPivot))
        (fun i : pivotComplement rowPivot ↦
          post.weight (case2ResidualRowLevel n S J i.1)) *
        pivotFirstMatrix rowPivot colPivot
          (case2SelectedNormalizedMatrix rowPivot colPivot residual) := by
  have hupdate :=
    hnew.case2_weight_succ_current_eq_newVar_mul pre post u
      hlevel_old hvar_old hlevel_new hvar_new
  have hpivot :
      u * pre.case2ResidualRowWeight rowPivot =
        post.weight (case2ResidualRowLevel n S J rowPivot) := by
    simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight] using
      (hupdate (case2ResidualRowLevel n S J rowPivot)
        (case2ResidualRowLevel_ge n S J rowPivot)).symm
  have hrows :
      (fun i : pivotComplement rowPivot ↦ u * pre.case2ResidualRowWeight i.1) =
      (fun i : pivotComplement rowPivot ↦
        post.weight (case2ResidualRowLevel n S J i.1)) := by
    funext i
    exact (by
      simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight] using
        (hupdate (case2ResidualRowLevel n S J i.1)
          (case2ResidualRowLevel_ge n S J i.1)).symm)
  rw [case2Selected_diagonal_mul_substitutionMatrix_pivotFirst]
  rw [hpivot, hrows]

/-- Arbitrary selected Case 2 source-variable transport from a supplied
recurrence post-data package. -/
theorem case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
        case2SelectedSubstitutionMatrix rowPivot colPivot u residual).submatrix
        (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot) =
      weightedPivotDiagonal
        (post.weight (case2ResidualRowLevel n S J rowPivot))
        (fun i : pivotComplement rowPivot ↦
          post.weight (case2ResidualRowLevel n S J i.1)) *
        pivotFirstMatrix rowPivot colPivot
          (case2SelectedNormalizedMatrix rowPivot colPivot residual) :=
  hnew.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights
    pre post u hpost.level_old hpost.var_old hpost.level_new hpost.var_new
    rowPivot colPivot residual

/-- Arbitrary selected Case 2 source-substitution `Q/P` identity with supplied
successor recurrence weights.  This is still conditional finite algebra for a
supplied pivot, not chart production or coverage. -/
theorem exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (hgap : pre.case2Gap) (u : R)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → post.level s k = pre.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → post.var s k = pre.var s k)
    (hlevel_new : post.level S (J + 1) = J)
    (hvar_new : post.var S (J + 1) = u)
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX rowPivot colPivot
              (case2SelectedNormalizedMatrix rowPivot colPivot residual) i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SelectedSubstitutionMatrix rowPivot colPivot u residual).submatrix
            (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)) *
          case2SelectedFollowingFactor colPivot C =
        (weightedPivotDiagonal
            (post.weight (case2ResidualRowLevel n S J rowPivot))
            (fun i : pivotComplement rowPivot ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot
                (case2SelectedNormalizedMatrix rowPivot colPivot residual) -
              pivotFirstX rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual) *
                pivotFirstY rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual))) *
          case2SelectedTransportedFollowingFactor rowPivot colPivot residual C := by
  rcases exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap
      L pre hgap rowPivot colPivot u residual C with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hupdate :=
    hnew.case2_weight_succ_current_eq_newVar_mul pre post u
      hlevel_old hvar_old hlevel_new hvar_new
  have hpivot :
      u * pre.case2ResidualRowWeight rowPivot =
        post.weight (case2ResidualRowLevel n S J rowPivot) := by
    simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight] using
      (hupdate (case2ResidualRowLevel n S J rowPivot)
        (case2ResidualRowLevel_ge n S J rowPivot)).symm
  have hrows :
      (fun i : pivotComplement rowPivot ↦ u * pre.case2ResidualRowWeight i.1) =
      (fun i : pivotComplement rowPivot ↦
        post.weight (case2ResidualRowLevel n S J i.1)) := by
    funext i
    exact (by
      simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight] using
        (hupdate (case2ResidualRowLevel n S J i.1)
          (case2ResidualRowLevel_ge n S J i.1)).symm)
  rwa [hpivot, hrows] at hq

/-- Arbitrary selected Case 2 source-substitution `Q/P` identity from a
supplied recurrence post-data package. -/
theorem exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (hgap : pre.case2Gap)
    (rowPivot : Case2ResidualRowIndex n S J)
    (colPivot : Case2ResidualColIndex n S J)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement rowPivot → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX rowPivot colPivot
              (case2SelectedNormalizedMatrix rowPivot colPivot residual) i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SelectedSubstitutionMatrix rowPivot colPivot u residual).submatrix
            (pivotFirstIndexEquiv rowPivot) (pivotFirstIndexEquiv colPivot)) *
          case2SelectedFollowingFactor colPivot C =
        (weightedPivotDiagonal
            (post.weight (case2ResidualRowLevel n S J rowPivot))
            (fun i : pivotComplement rowPivot ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD rowPivot colPivot
                (case2SelectedNormalizedMatrix rowPivot colPivot residual) -
              pivotFirstX rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual) *
                pivotFirstY rowPivot colPivot
                  (case2SelectedNormalizedMatrix rowPivot colPivot residual))) *
          case2SelectedTransportedFollowingFactor rowPivot colPivot residual C :=
  hnew.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights
    pre post hgap u hpost.level_old hpost.var_old hpost.level_new hpost.var_new
    rowPivot colPivot residual C

end CorrectedCase2NewLabelCertificate

/-- Restrict source-coordinate residual data to the Case 2 residual block.
Rows are the prefix-minimum residual rows and columns are the actual-width
residual columns. -/
def case2SourceResidualBlock
    {n : ℕ → ℕ} {S J : ℕ}
    (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  fun i j ↦ residual (i.1, j.1)

/-- Restrict a source-coordinate following factor to the Case 2 residual
columns. -/
def case2SourceFollowingFactor
    {n : ℕ → ℕ} {S J : ℕ}
    (C : ℕ → τ → R) :
    Matrix (Case2ResidualColIndex n S J) τ R :=
  fun j t ↦ C j.1 t

/-- Source row indices already above the displayed Case 2 residual block.

These correspond to the old top rows `1,...,J` in Aoyagi's stopped Case 2
terminal display. -/
abbrev case2SourceOldTopRowIndex (J : ℕ) : Type :=
  (Finset.Icc 1 J : Type)

/-- Source old-top diagonal weights `diag(b_1,...,b_J)`.

This is a source-shaped specialization of the previously supplied old top
multiplier; it does not construct the remaining suffix product. -/
def case2DisplayedSourceOldTopWeight
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (pre : IntroducedLabelRecurrenceState L n S J R) :
    Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R :=
  diagonal (fun i ↦ pre.weight i.1)

/-- Source old-top rows `1,...,J` of the following matrix. -/
def case2DisplayedSourceOldTopBlock
    {J : ℕ} (C : ℕ → τ → R) :
    Matrix (case2SourceOldTopRowIndex J) τ R :=
  fun i t ↦ C i.1 t

/-- Source terminal rows `1,...,J+1` after the stopped displayed Case 2
pivot row survives. -/
abbrev case2SourceTerminalRowIndex (J : ℕ) : Type :=
  (Finset.Icc 1 (J + 1) : Type)

/-- Source terminal prefix rows `1,...,M(S+1)` in the stopped displayed Case 2
terminal display. -/
abbrev case2SourceTerminalPrefixRowIndex (n : ℕ → ℕ) (S : ℕ) : Type :=
  (Finset.Icc 1 (prefixMinNat n (S + 1)) : Type)

/-- Reindex the stacked old rows plus surviving pivot row by source rows
`1,...,J+1`. -/
def case2SourceTerminalRowEquiv (J : ℕ) :
    case2SourceOldTopRowIndex J ⊕ Unit ≃ case2SourceTerminalRowIndex J where
  toFun
    | Sum.inl i => ⟨i.1, Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp i.2).1,
          le_trans (Finset.mem_Icc.mp i.2).2 (by omega : J ≤ J + 1)⟩⟩
    | Sum.inr _ => ⟨J + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  invFun i :=
    if h : i.1 ≤ J then
      Sum.inl ⟨i.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp i.2).1, h⟩⟩
    else Sum.inr ()
  left_inv := by
    intro i
    rcases i with i | u
    · simp [show i.1 ≤ J from (Finset.mem_Icc.mp i.2).2]
    · simp
  right_inv := by
    intro i
    by_cases h : i.1 ≤ J
    · simp [h]
    · have hi : i.1 = J + 1 := by
        have hle := (Finset.mem_Icc.mp i.2).2
        omega
      ext
      simp [hi]

@[simp] theorem case2SourceTerminalRowEquiv_inl (J : ℕ)
    (i : case2SourceOldTopRowIndex J) :
    (case2SourceTerminalRowEquiv J (Sum.inl i) : ℕ) = i.1 :=
  rfl

@[simp] theorem case2SourceTerminalRowEquiv_inr (J : ℕ) (u : Unit) :
    (case2SourceTerminalRowEquiv J (Sum.inr u) : ℕ) = J + 1 :=
  rfl

/-- Under a terminal-frontier equality, source terminal rows `1,...,J+1`
are the same finite type as the terminal prefix rows `1,...,M(S+1)`. -/
def case2SourceTerminalRowEquivPrefix
    (n : ℕ → ℕ) {S J : ℕ}
    (hfront : prefixMinNat n (S + 1) = J + 1) :
    case2SourceTerminalRowIndex J ≃ case2SourceTerminalPrefixRowIndex n S where
  toFun i := ⟨i.1, by
    rw [hfront]
    exact i.2⟩
  invFun i := ⟨i.1, by
    rw [← hfront]
    exact i.2⟩
  left_inv i := by
    ext
    rfl
  right_inv i := by
    ext
    rfl

@[simp] theorem case2SourceTerminalRowEquivPrefix_apply_coe
    (n : ℕ → ℕ) {S J : ℕ}
    (hfront : prefixMinNat n (S + 1) = J + 1)
    (i : case2SourceTerminalRowIndex J) :
    ((case2SourceTerminalRowEquivPrefix n hfront i : ℕ) = i.1) :=
  rfl

@[simp] theorem case2SourceTerminalRowEquivPrefix_symm_apply_coe
    (n : ℕ → ℕ) {S J : ℕ}
    (hfront : prefixMinNat n (S + 1) = J + 1)
    (i : case2SourceTerminalPrefixRowIndex n S) :
    (((case2SourceTerminalRowEquivPrefix n hfront).symm i : ℕ) = i.1) :=
  rfl

/-- Stopped displayed Case 2 continuation identifies source terminal rows with
the terminal prefix row range. -/
def case2SourceTerminalRowEquivPrefixOfNotNext
    (n : ℕ → ℕ) {S J : ℕ}
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1)) :
    case2SourceTerminalRowIndex J ≃ case2SourceTerminalPrefixRowIndex n S :=
  case2SourceTerminalRowEquivPrefix n
    (case2_next_frontier_eq_of_cont_of_not_next hcont hstop)

/-- Source-coordinate specialization of the elementary Case 1(1) selected-old
row-strip identity.

The source residual function is restricted to residual rows `J+1..mu_S` and
actual-width residual columns `J+1..n_(S+1)`.  This is only the row-wise
source-coordinate algebra for the selected-old chart denominator; it does not
introduce the displayed Case 1(2) pivot label or assert a `Q/P` transition. -/
theorem case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates
    {R : Type*} [CommRing R] {n : ℕ → ℕ} {S J : ℕ} (J1 : ℕ)
    (u : R) (baseWeight : Case2ResidualRowIndex n S J → R)
    (residual : ℕ × ℕ → R) :
    diagonal baseWeight *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u
          (case2SourceResidualBlock residual) =
      diagonal
          (case1SelectedOldPostWeight
            (case1ResidualRowStrip n S J J1) u baseWeight) *
        case2SourceResidualBlock residual :=
  case1SelectedOld_diagonal_mul_sourceMatrix
    (case1ResidualRowStrip n S J J1) u baseWeight
    (case2SourceResidualBlock residual)

/-- Source-coordinate Case 1(1) row-strip identity with the right diagonal
written as the recurrence obtained by lowering the selected old factor from
level `J+J1` to level `J`. -/
theorem case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates_loweredLevel
    {R : Type*} [CommRing R] {n : ℕ → ℕ} {S J : ℕ} (J1 : ℕ)
    (step : ℕ → R) (u : R) (residual : ℕ × ℕ → R) :
    diagonal
        (fun i ↦ monomialRec (mulStepAt step u (J + J1))
          (case2ResidualRowLevel n S J i)) *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u
          (case2SourceResidualBlock residual) =
      diagonal
        (fun i ↦ monomialRec (mulStepAt step u J)
          (case2ResidualRowLevel n S J i)) *
        case2SourceResidualBlock residual :=
  case1SelectedOld_diagonal_mul_sourceMatrix_loweredLevel
    step u n S J J1 (case2SourceResidualBlock residual)

/-- Supplied same-domain boundary for Aoyagi Case 1(1)'s selected-old chart.

The boundary combines the selected old label, pre-exponent certificates,
level/tail invariants, and supplied same-domain exponent post-data.  It exports
the elementary row-strip source-coordinate identity and the same-domain
selected-label exponent update as separate projections.  It does not construct
the selected-old chart, introduce `(S,J+1)`, assert a `Q/P` transition, or
prove coverage, regularity, Jacobians, normal crossings, or RLCT extraction. -/
structure Case1SelectedOldSuppliedSameDomainBoundary
    (L : ℕ) (n : ℕ → ℕ) (S J J1 s0 k0 : ℕ)
    (level : ℕ → ℕ → ℕ)
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ) : Prop where
  firstJump : Case1FirstJumpHypotheses L n S J J1 s0 k0 level t
  stage_ge_two : 2 ≤ S
  stage_le : S ≤ L
  exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue
  levelTail : IntroducedLabelLevelTailInvariants L n S J level t leastValue
  exponentPost :
    Case1SelectedOldLowerTailExponentPostData
      (L := L) (n := n) (S := S) (J := J) (J1 := J1) (s0 := s0) (k0 := k0)
      t t' numerator numerator' leastValue leastValue'

namespace Case1SelectedOldSuppliedSameDomainBoundary

/-- The supplied Case 1(1) boundary records the selected old label as already
introduced at the current state. -/
theorem selectedIntroduced
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (data :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue') :
    introducedLabel L n S J s0 k0 :=
  data.firstJump.selectedIntroduced

/-- The selected old label sits at the first jumped level `J+J1`. -/
theorem selectedLevel
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (data :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue') :
    level s0 k0 = J + J1 :=
  data.firstJump.selectedLevel

/-- The row-wise Case 1(1) selected-old source identity on the residual block.
This is only the divided-row algebra; it does not produce exponent post-data. -/
theorem sourceMatrix_identity
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (_data :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue')
    (u : R) (baseWeight : Case2ResidualRowIndex n S J → R)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R) :
    diagonal baseWeight *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A =
      diagonal
          (case1SelectedOldPostWeight
            (case1ResidualRowStrip n S J J1) u baseWeight) *
        A :=
  case1SelectedOld_diagonal_mul_sourceMatrix
    (case1ResidualRowStrip n S J J1) u baseWeight A

/-- Source-coordinate form of the Case 1(1) selected-old row-strip identity.
The source residual function is only restricted to the residual block; no
displayed pivot normalization or `Q/P` step is involved. -/
theorem sourceCoordinates_identity
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (_data :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue')
    (u : R) (baseWeight : Case2ResidualRowIndex n S J → R)
    (residual : ℕ × ℕ → R) :
    diagonal baseWeight *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u
          (case2SourceResidualBlock residual) =
      diagonal
          (case1SelectedOldPostWeight
            (case1ResidualRowStrip n S J J1) u baseWeight) *
        case2SourceResidualBlock residual :=
  case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates J1
    u baseWeight residual

/-- The supplied Case 1(1) boundary updates exponent certificates over the
same introduced-label domain `(S,J)`. -/
theorem updateExponentCertificates
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (data :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue') :
    IntroducedLabelExponentCertificates L n S J t' numerator' leastValue' :=
  data.exponentPre.case1_selectedLowerTail_of_levelTailInvariants_postData
    data.firstJump data.levelTail data.stage_ge_two data.stage_le data.exponentPost

end Case1SelectedOldSuppliedSameDomainBoundary

/-- Supplied recurrence-state boundary for Aoyagi Case 1(1)'s selected-old
level lowering.

The `baseStep` recurrence is supplied: `pre` has the selected old factor at
level `J+J1`, while `post` has the same factor moved down to level `J`.
The same-domain exponent boundary is carried separately.  This does not
construct the selected-old chart or derive the base recurrence from source
coordinates. -/
structure Case1SelectedOldLoweredRecurrenceBoundary
    (R : Type*) [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J J1 s0 k0 : ℕ)
    (level : ℕ → ℕ → ℕ)
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ)
    (pre post : IntroducedLabelRecurrenceState L n S J R)
    (u : R) (baseStep : ℕ → R) : Prop where
  sameDomain :
    Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 level
      t t' numerator numerator' leastValue leastValue'
  pre_step_eq : pre.step = mulStepAt baseStep u (J + J1)
  post_step_eq : post.step = mulStepAt baseStep u J

namespace Case1SelectedOldLoweredRecurrenceBoundary

/-- The erased-selected-label recurrence model instantiates the supplied
lowered-recurrence boundary.

Here `baseStep` is not arbitrary: it is the finite product recurrence with the
selected old label `(s0,k0)` erased.  The moved-level data says that the pre
state reinserts that label at level `J+J1`, while the post state reinserts the
same selected variable at level `J`, with all non-selected introduced-label
data unchanged.  This remains recurrence bookkeeping, not chart construction.
-/
theorem of_levelMoveData
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R}
    (sameDomain :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 pre.level
        t t' numerator numerator' leastValue leastValue')
    (moved :
      IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData
        (J1 := J1) pre post s0 k0 u) :
    Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 pre.level
      t t' numerator numerator' leastValue leastValue'
      pre post u (pre.erasedStep s0 k0) where
  sameDomain := sameDomain
  pre_step_eq := moved.pre_step_eq_mulStepAt
  post_step_eq := moved.post_step_eq_mulStepAt

/-- Concrete same-domain Case 1(1) lowered boundary obtained by lowering only
the selected old label's recurrence level in the pre-state.

This is a canonical recurrence-state witness for the already supplied
same-domain exponent boundary.  It uses `sameDomain` stated with `pre.level`;
no chart construction or separate level-map transport is hidden here.
-/
theorem of_sameDomain_case1SelectedOldLevelMove
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (sameDomain :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 pre.level
        t t' numerator numerator' leastValue leastValue') :
    Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 pre.level
      t t' numerator numerator' leastValue leastValue'
      pre (pre.case1SelectedOldLevelMove s0 k0) (pre.var s0 k0)
      (pre.erasedStep s0 k0) :=
  of_levelMoveData sameDomain
    (pre.case1SelectedOldLevelMove_levelMoveData sameDomain.selectedIntroduced
      sameDomain.selectedLevel)

/-- The supplied lowered-recurrence boundary records the selected old label as
already introduced at the current state. -/
theorem selectedIntroduced
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    (data :
      Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep) :
    introducedLabel L n S J s0 k0 :=
  data.sameDomain.selectedIntroduced

/-- The selected old label has the first-jump level `J+J1`. -/
theorem selectedLevel
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    (data :
      Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep) :
    level s0 k0 = J + J1 :=
  data.sameDomain.selectedLevel

/-- The piecewise Case 1(1) post-weight convention equals the supplied lowered
post recurrence weights on residual rows. -/
theorem selectedOldPostWeight_eq_postWeight
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    (data :
      Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep) :
    case1SelectedOldPostWeight (case1ResidualRowStrip n S J J1) u
        (fun i ↦ pre.weight (case2ResidualRowLevel n S J i)) =
      fun i ↦ post.weight (case2ResidualRowLevel n S J i) := by
  change case1SelectedOldPostWeight (case1ResidualRowStrip n S J J1) u
      (fun i ↦ monomialRec pre.step (case2ResidualRowLevel n S J i)) =
    fun i ↦ monomialRec post.step (case2ResidualRowLevel n S J i)
  rw [data.pre_step_eq, data.post_step_eq]
  exact case1SelectedOldPostWeight_eq_monomialRec_loweredLevel
    baseStep u n S J J1

/-- The selected-old lowered recurrence boundary rewrites the Case 1(1)
source identity with supplied pre and post recurrence weights. -/
theorem sourceMatrix_identity_postWeights
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    (data :
      Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R) :
    diagonal (fun i ↦ pre.weight (case2ResidualRowLevel n S J i)) *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A =
      diagonal (fun i ↦ post.weight (case2ResidualRowLevel n S J i)) * A := by
  calc
    diagonal (fun i ↦ pre.weight (case2ResidualRowLevel n S J i)) *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A
        = diagonal
            (case1SelectedOldPostWeight (case1ResidualRowStrip n S J J1) u
              (fun i ↦ pre.weight (case2ResidualRowLevel n S J i))) *
            A := by
              exact case1SelectedOld_diagonal_mul_sourceMatrix
                (case1ResidualRowStrip n S J J1) u
                (fun i ↦ pre.weight (case2ResidualRowLevel n S J i)) A
    _ = diagonal (fun i ↦ post.weight (case2ResidualRowLevel n S J i)) * A := by
              rw [data.selectedOldPostWeight_eq_postWeight]

/-- Source-coordinate form of the supplied pre/post recurrence-weight Case
1(1) selected-old identity. -/
theorem sourceCoordinates_identity_postWeights
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    (data :
      Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep)
    (residual : ℕ × ℕ → R) :
    diagonal (fun i ↦ pre.weight (case2ResidualRowLevel n S J i)) *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u
          (case2SourceResidualBlock residual) =
      diagonal (fun i ↦ post.weight (case2ResidualRowLevel n S J i)) *
        case2SourceResidualBlock residual :=
  data.sourceMatrix_identity_postWeights (case2SourceResidualBlock residual)

/-- The supplied lowered-recurrence boundary carries the same-domain exponent
certificate update from the selected-old Case 1(1) boundary. -/
theorem updateExponentCertificates
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    (data :
      Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep) :
    IntroducedLabelExponentCertificates L n S J t' numerator' leastValue' :=
  data.sameDomain.updateExponentCertificates

end Case1SelectedOldLoweredRecurrenceBoundary

/-- Supplied chart-family boundary for Aoyagi Case 1(1)'s selected-old `Unit`
chart.

This combines the supplied selected-old lowered-recurrence boundary with a
supplied finite Case 1 chart-family boundary.  The `Unit` token is only the
finite center generator for the selected old chart; selected-label facts still
come from the carried first-jump data. -/
structure Case1SelectedOldUnitSuppliedChartFamilyBoundary
    (R : Type*) [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J J1 s0 k0 : ℕ)
    (level : ℕ → ℕ → ℕ)
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ)
    (pre post : IntroducedLabelRecurrenceState L n S J R)
    (u : R) (baseStep : ℕ → R)
    (ChartRegular : Case1CenterGenerator → Prop)
    (TransitionRegular :
      Case1CenterGenerator → Case1CenterGenerator → Prop) : Prop where
  lowered :
    Case1SelectedOldLoweredRecurrenceBoundary R L n S J J1 s0 k0 level
      t t' numerator numerator' leastValue leastValue'
      pre post u baseStep
  chartFamily :
    Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular

namespace Case1SelectedOldUnitSuppliedChartFamilyBoundary

/-- Concrete same-domain selected-old `Unit` chart-family boundary obtained by
lowering only the selected old label's recurrence level and carrying a supplied
finite chart family. -/
theorem of_sameDomain_case1SelectedOldLevelMove
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (sameDomain :
      Case1SelectedOldSuppliedSameDomainBoundary L n S J J1 s0 k0 pre.level
        t t' numerator numerator' leastValue leastValue')
    (chartFamily :
      Case1CenterChartFamilyBoundary n S J J1 ChartRegular TransitionRegular) :
    Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 pre.level
      t t' numerator numerator' leastValue leastValue'
      pre (pre.case1SelectedOldLevelMove s0 k0) (pre.var s0 k0)
      (pre.erasedStep s0 k0) ChartRegular TransitionRegular where
  lowered :=
    Case1SelectedOldLoweredRecurrenceBoundary.of_sameDomain_case1SelectedOldLevelMove
      pre sameDomain
  chartFamily := chartFamily

/-- The supplied selected-old `Unit` chart boundary records the selected old
label as introduced through the carried first-jump data. -/
theorem selectedIntroduced
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular) :
    introducedLabel L n S J s0 k0 :=
  data.lowered.selectedIntroduced

/-- The selected old label has the first-jump level `J+J1`. -/
theorem selectedLevel
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular) :
    level s0 k0 = J + J1 :=
  data.lowered.selectedLevel

/-- The selected old `Unit` token is in the finite Case 1 center.  This is
finite-center membership only, not a derivation of `(s0,k0)` from the token. -/
theorem selectedOld_mem_center
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (_data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular) :
    (Sum.inl () : Case1CenterGenerator) ∈ case1CenterGenerators n S J J1 :=
  case1_selectedOld_mem_center n S J J1

/-- Supplied chart-family regularity for the selected-old `Unit` chart. -/
theorem chart_regular_selectedOld
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular) :
    ChartRegular (Sum.inl () : Case1CenterGenerator) :=
  Case1CenterChartFamilyBoundary.chart_regular_of_mem data.chartFamily
    data.selectedOld_mem_center

/-- Supplied transition regularity from the selected-old chart token to any
finite Case 1 center generator. -/
theorem transition_regular_selectedOld_of_mem
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular)
    {g : Case1CenterGenerator} (hg : g ∈ case1CenterGenerators n S J J1) :
    TransitionRegular (Sum.inl () : Case1CenterGenerator) g :=
  Case1CenterChartFamilyBoundary.transition_regular_of_mem data.chartFamily
    data.selectedOld_mem_center hg

/-- Supplied transition regularity from any finite Case 1 center generator to
the selected-old chart token. -/
theorem transition_regular_of_mem_selectedOld
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular)
    {g : Case1CenterGenerator} (hg : g ∈ case1CenterGenerators n S J J1) :
    TransitionRegular g (Sum.inl () : Case1CenterGenerator) :=
  Case1CenterChartFamilyBoundary.transition_regular_of_mem data.chartFamily
    hg data.selectedOld_mem_center

/-- In the selected-old `Unit` chart, the selected variable occurs as a value
of the transformed finite Case 1 center. -/
theorem selectedOld_selectedEntryChartMap_value_mem
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (_data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular)
    (residual : Case1CenterGenerator → R) :
    u ∈
      {v : R | ∃ g, g ∈ case1CenterGenerators n S J J1 ∧
        selectedEntryChartMap (Sum.inl () : Case1CenterGenerator) u residual g = v} :=
  case1_selectedOld_selectedEntryChartMap_value_mem n S J J1 u residual

/-- In the selected-old `Unit` chart, every transformed finite Case 1 center
generator is divisible by the selected old chart variable. -/
theorem selectedOld_center_dvd
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular)
    (residual : Case1CenterGenerator → R) :
    ∀ g, g ∈ case1CenterGenerators n S J J1 →
      u ∣ selectedEntryChartMap
        (Sum.inl () : Case1CenterGenerator) u residual g :=
  case1_selectedEntryChartMap_center_dvd_of_mem data.selectedOld_mem_center u residual

/-- In the selected-old `Unit` chart, the transformed finite Case 1 center
ideal is the principal ideal generated by the selected old chart variable. -/
theorem selectedOld_centerIdeal_eq_span_singleton
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular)
    (residual : Case1CenterGenerator → R) :
    Ideal.span
        {v : R | ∃ g, g ∈ case1CenterGenerators n S J J1 ∧
          selectedEntryChartMap (Sum.inl () : Case1CenterGenerator)
            u residual g = v} =
      Ideal.span ({u} : Set R) :=
  case1_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem
    data.selectedOld_mem_center u residual

/-- The selected-old `Unit` chart-family boundary preserves the supplied
pre/post recurrence-weight source identity. -/
theorem sourceMatrix_identity_postWeights
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular)
    (A : Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R) :
    diagonal (fun i ↦ pre.weight (case2ResidualRowLevel n S J i)) *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u A =
      diagonal (fun i ↦ post.weight (case2ResidualRowLevel n S J i)) * A :=
  data.lowered.sourceMatrix_identity_postWeights A

/-- Source-coordinate form of the selected-old `Unit` chart-family boundary's
pre/post recurrence-weight identity. -/
theorem sourceCoordinates_identity_postWeights
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) :
    diagonal (fun i ↦ pre.weight (case2ResidualRowLevel n S J i)) *
        case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u
          (case2SourceResidualBlock residual) =
      diagonal (fun i ↦ post.weight (case2ResidualRowLevel n S J i)) *
        case2SourceResidualBlock residual :=
  data.lowered.sourceCoordinates_identity_postWeights residual

/-- The selected-old `Unit` chart-family boundary carries the same-domain
exponent certificate update. -/
theorem updateExponentCertificates
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState L n S J R}
    {u : R} {baseStep : ℕ → R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary R L n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular) :
    IntroducedLabelExponentCertificates L n S J t' numerator' leastValue' :=
  data.lowered.updateExponentCertificates

end Case1SelectedOldUnitSuppliedChartFamilyBoundary

/-- Source-coordinate normalised matrix for a supplied Case 2 residual-block
pivot pair.  The membership proof only extracts row and column subtype pivots;
it is not a chart-coverage assertion. -/
def case2SourceSelectedNormalizedMatrixOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  case2SelectedNormalizedMatrix
    (case2ResidualBlockPivotRowOfMem hp)
    (case2ResidualBlockPivotColOfMem hp)
    (case2SourceResidualBlock residual)

/-- Source-coordinate selected-entry substitution matrix for a supplied Case 2
residual-block pivot pair. -/
def case2SourceSelectedSubstitutionMatrixOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (u : R) (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  case2SelectedSubstitutionMatrix
    (case2ResidualBlockPivotRowOfMem hp)
    (case2ResidualBlockPivotColOfMem hp)
    u (case2SourceResidualBlock residual)

/-- Source-coordinate following factor reindexed into the selected pivot-first
column order. -/
def case2SourceSelectedFollowingFactorOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (C : ℕ → τ → R) :
    Matrix (Unit ⊕ pivotComplement (case2ResidualBlockPivotColOfMem hp)) τ R :=
  case2SelectedFollowingFactor
    (case2ResidualBlockPivotColOfMem hp)
    (case2SourceFollowingFactor C)

/-- Source-coordinate following factor after the arbitrary selected-pivot
`Q⁻¹ C` transport. -/
def case2SourceSelectedTransportedFollowingFactorOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (Unit ⊕ pivotComplement (case2ResidualBlockPivotColOfMem hp)) τ R :=
  case2SelectedTransportedFollowingFactor
    (case2ResidualBlockPivotRowOfMem hp)
    (case2ResidualBlockPivotColOfMem hp)
    (case2SourceResidualBlock residual)
    (case2SourceFollowingFactor C)

/-- Source-coordinate selected-entry chart map for a supplied Case 2
residual-block pivot.  The pivot is supplied as a member of the finite center;
the membership proof certifies only the selected pivot, while the map remains
total on source coordinate pairs.  This is not chart coverage or a
source-displayed arbitrary-pivot formula. -/
def case2SourceSelectedChartMapOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (_hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (u : R) (residual : ℕ × ℕ → R) (q : ℕ × ℕ) : R :=
  selectedEntryChartMap p u residual q

/-- Source-coordinate normalised map for a supplied Case 2 residual-block
pivot.  The membership proof certifies only the selected pivot; the map remains
total on source coordinate pairs. -/
def case2SourceSelectedNormalizedMapOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (_hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (residual : ℕ × ℕ → R) (q : ℕ × ℕ) : R :=
  selectedEntryNormalizedMap p residual q

@[simp] theorem case2SourceSelectedChartMapOfMem_pivot
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (u : R) (residual : ℕ × ℕ → R) :
    case2SourceSelectedChartMapOfMem hp u residual p = u := by
  simp [case2SourceSelectedChartMapOfMem]

@[simp] theorem case2SourceSelectedNormalizedMapOfMem_pivot
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (residual : ℕ × ℕ → R) :
    case2SourceSelectedNormalizedMapOfMem hp residual p = 1 := by
  simp [case2SourceSelectedNormalizedMapOfMem]

theorem case2SourceSelectedChartMapOfMem_of_ne
    {n : ℕ → ℕ} {S J : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (u : R) (residual : ℕ × ℕ → R) (hq : q ≠ p) :
    case2SourceSelectedChartMapOfMem hp u residual q = u * residual q := by
  exact selectedEntryChartMap_of_ne u residual hq

theorem case2SourceSelectedChartMapOfMem_eq_mul_normalized
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (u : R) (residual : ℕ × ℕ → R) (q : ℕ × ℕ) :
    case2SourceSelectedChartMapOfMem hp u residual q =
      u * case2SourceSelectedNormalizedMapOfMem hp residual q :=
  rfl

omit [CommRing R] [Fintype κ] [DecidableEq κ] in
/-- Equality with the supplied source pair is the same as equality with the
extracted residual-block row and column pivot. -/
theorem case2SourceSelected_source_pair_eq_pivot_iff
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (i : Case2ResidualRowIndex n S J)
    (j : Case2ResidualColIndex n S J) :
    (i.1, j.1) = p ↔
      (i, j) =
        (case2ResidualBlockPivotRowOfMem hp,
         case2ResidualBlockPivotColOfMem hp) := by
  constructor
  · intro h
    rcases Prod.ext_iff.mp h with ⟨hi, hj⟩
    apply Prod.ext
    · exact Subtype.ext hi
    · exact Subtype.ext hj
  · intro h
    cases h
    exact case2ResidualBlockPivotOfMem_pair hp

/-- Source-coordinate selected-entry substitution block for a supplied Case 2
pivot, restricted to residual rows and columns. -/
def case2SourceSelectedSubstitutionBlockOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (u : R) (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  fun i j ↦ case2SourceSelectedChartMapOfMem hp u residual (i.1, j.1)

/-- Source-coordinate normalised selected-entry block for a supplied Case 2
pivot, restricted to residual rows and columns. -/
def case2SourceSelectedNormalizedBlockOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  fun i j ↦ case2SourceSelectedNormalizedMapOfMem hp residual (i.1, j.1)

/-- The source-coordinate normalised block agrees with the existing
source-selected normalised matrix after restricting source residuals. -/
theorem case2SourceSelectedNormalizedBlockOfMem_eq_selectedNormalizedMatrixOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (residual : ℕ × ℕ → R) :
    case2SourceSelectedNormalizedBlockOfMem hp residual =
      case2SourceSelectedNormalizedMatrixOfMem hp residual := by
  ext i j
  by_cases hsrc : (i.1, j.1) = p
  · have hsub := (case2SourceSelected_source_pair_eq_pivot_iff hp i j).1 hsrc
    cases hsub
    simp [case2SourceSelectedNormalizedBlockOfMem,
      case2SourceSelectedNormalizedMapOfMem,
      case2SourceSelectedNormalizedMatrixOfMem, case2SelectedNormalizedMatrix]
  · have hsub :
        (i, j) ≠
          (case2ResidualBlockPivotRowOfMem hp,
           case2ResidualBlockPivotColOfMem hp) := by
      intro h
      exact hsrc ((case2SourceSelected_source_pair_eq_pivot_iff hp i j).2 h)
    rw [case2SourceSelectedNormalizedBlockOfMem,
      case2SourceSelectedNormalizedMapOfMem,
      case2SourceSelectedNormalizedMatrixOfMem, case2SelectedNormalizedMatrix]
    rw [selectedEntryNormalizedMap_of_ne residual hsrc]
    rw [selectedEntryNormalizedMatrix_of_ne (case2SourceResidualBlock residual) hsub]
    rfl

/-- The source-coordinate substituted block agrees with the existing
source-selected substitution matrix after restricting source residuals. -/
theorem case2SourceSelectedSubstitutionBlockOfMem_eq_selectedSubstitutionMatrixOfMem
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (u : R) (residual : ℕ × ℕ → R) :
    case2SourceSelectedSubstitutionBlockOfMem hp u residual =
      case2SourceSelectedSubstitutionMatrixOfMem hp u residual := by
  ext i j
  by_cases hsrc : (i.1, j.1) = p
  · have hsub := (case2SourceSelected_source_pair_eq_pivot_iff hp i j).1 hsrc
    cases hsub
    simp [case2SourceSelectedSubstitutionBlockOfMem,
      case2SourceSelectedChartMapOfMem,
      case2SourceSelectedSubstitutionMatrixOfMem, case2SelectedSubstitutionMatrix]
  · have hsub :
        (i, j) ≠
          (case2ResidualBlockPivotRowOfMem hp,
           case2ResidualBlockPivotColOfMem hp) := by
      intro h
      exact hsrc ((case2SourceSelected_source_pair_eq_pivot_iff hp i j).2 h)
    simp [case2SourceSelectedSubstitutionBlockOfMem,
      case2SourceSelectedChartMapOfMem,
      case2SourceSelectedSubstitutionMatrixOfMem, case2SelectedSubstitutionMatrix,
      selectedEntrySubstitutionMatrix,
      selectedEntryChartMap, case2SourceResidualBlock, hsrc, hsub]

@[simp] theorem case2SourceSelectedNormalizedMatrixOfMem_pivot
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (residual : ℕ × ℕ → R) :
    case2SourceSelectedNormalizedMatrixOfMem hp residual
      (case2ResidualBlockPivotRowOfMem hp)
      (case2ResidualBlockPivotColOfMem hp) = 1 := by
  simp [case2SourceSelectedNormalizedMatrixOfMem, case2SelectedNormalizedMatrix]

@[simp] theorem case2SourceSelectedSubstitutionMatrixOfMem_pivot
    {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (u : R) (residual : ℕ × ℕ → R) :
    case2SourceSelectedSubstitutionMatrixOfMem hp u residual
      (case2ResidualBlockPivotRowOfMem hp)
      (case2ResidualBlockPivotColOfMem hp) = u := by
  simp [case2SourceSelectedSubstitutionMatrixOfMem, case2SelectedSubstitutionMatrix]

/-- Source-coordinate Case 2 selected-pivot `Q/P` identity for a source pivot
pair known to lie in the residual-block center and an old recurrence state
satisfying the Case 2 gap.  This is a wrapper around finite algebra for a
supplied pivot pair; it does not prove chart production or chart coverage. -/
theorem exists_case2SourceSelectedQP_mul_sourceSubstitution_of_recurrenceStateGap
    (L : ℕ) {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (state : IntroducedLabelRecurrenceState L n S J R)
    (hgap : state.case2Gap) (u : R)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    ∃ q : pivotComplement (case2ResidualBlockPivotRowOfMem hp) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2ResidualBlockPivotRowOfMem hp)
              (case2ResidualBlockPivotColOfMem hp)
              (case2SourceSelectedNormalizedMatrixOfMem hp residual) i ()) *
          (diagonal (fun i ↦ state.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionMatrixOfMem hp u residual).submatrix
            (pivotFirstIndexEquiv (case2ResidualBlockPivotRowOfMem hp))
            (pivotFirstIndexEquiv (case2ResidualBlockPivotColOfMem hp))) *
          case2SourceSelectedFollowingFactorOfMem hp C =
        (weightedPivotDiagonal
            (u * state.case2ResidualRowWeight
              (case2ResidualBlockPivotRowOfMem hp))
            (fun i : pivotComplement (case2ResidualBlockPivotRowOfMem hp) ↦
              u * state.case2ResidualRowWeight i.1) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2ResidualBlockPivotRowOfMem hp)
                (case2ResidualBlockPivotColOfMem hp)
                (case2SourceSelectedNormalizedMatrixOfMem hp residual) -
              pivotFirstX
                  (case2ResidualBlockPivotRowOfMem hp)
                  (case2ResidualBlockPivotColOfMem hp)
                  (case2SourceSelectedNormalizedMatrixOfMem hp residual) *
                pivotFirstY
                  (case2ResidualBlockPivotRowOfMem hp)
                  (case2ResidualBlockPivotColOfMem hp)
                  (case2SourceSelectedNormalizedMatrixOfMem hp residual))) *
          case2SourceSelectedTransportedFollowingFactorOfMem hp residual C := by
  simpa [case2SourceSelectedNormalizedMatrixOfMem,
    case2SourceSelectedSubstitutionMatrixOfMem,
    case2SourceSelectedFollowingFactorOfMem,
    case2SourceSelectedTransportedFollowingFactorOfMem,
    case2SourceResidualBlock, case2SourceFollowingFactor] using
    exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap
      L state hgap
      (case2ResidualBlockPivotRowOfMem hp)
      (case2ResidualBlockPivotColOfMem hp)
      u (case2SourceResidualBlock residual) (case2SourceFollowingFactor C)

namespace CorrectedCase2NewLabelCertificate

/-- Source-coordinate selected-pivot source-variable transport from a supplied
successor recurrence post-data package. -/
theorem case2SourceSelected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (residual : ℕ × ℕ → R) :
    (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
        case2SourceSelectedSubstitutionMatrixOfMem hp u residual).submatrix
        (pivotFirstIndexEquiv (case2ResidualBlockPivotRowOfMem hp))
        (pivotFirstIndexEquiv (case2ResidualBlockPivotColOfMem hp)) =
      weightedPivotDiagonal
        (post.weight
          (case2ResidualRowLevel n S J (case2ResidualBlockPivotRowOfMem hp)))
        (fun i : pivotComplement (case2ResidualBlockPivotRowOfMem hp) ↦
          post.weight (case2ResidualRowLevel n S J i.1)) *
        pivotFirstMatrix
          (case2ResidualBlockPivotRowOfMem hp)
          (case2ResidualBlockPivotColOfMem hp)
          (case2SourceSelectedNormalizedMatrixOfMem hp residual) := by
  simpa [case2SourceSelectedNormalizedMatrixOfMem,
    case2SourceSelectedSubstitutionMatrixOfMem, case2SourceResidualBlock] using
    hnew.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData
      hpost
      (case2ResidualBlockPivotRowOfMem hp)
      (case2ResidualBlockPivotColOfMem hp)
      (case2SourceResidualBlock residual)

/-- Source-coordinate selected-pivot `Q/P` identity from a source pivot pair,
old Case 2 gap, and supplied successor recurrence post-data.  This remains
conditional finite algebra for the supplied pair, not arbitrary-pivot chart
coverage. -/
theorem exists_case2SourceSelectedQP_of_recurrenceStateGap_succWeights_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (hgap : pre.case2Gap)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    ∃ q : pivotComplement (case2ResidualBlockPivotRowOfMem hp) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2ResidualBlockPivotRowOfMem hp)
              (case2ResidualBlockPivotColOfMem hp)
              (case2SourceSelectedNormalizedMatrixOfMem hp residual) i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionMatrixOfMem hp u residual).submatrix
            (pivotFirstIndexEquiv (case2ResidualBlockPivotRowOfMem hp))
            (pivotFirstIndexEquiv (case2ResidualBlockPivotColOfMem hp))) *
          case2SourceSelectedFollowingFactorOfMem hp C =
        (weightedPivotDiagonal
            (post.weight
              (case2ResidualRowLevel n S J
                (case2ResidualBlockPivotRowOfMem hp)))
            (fun i : pivotComplement (case2ResidualBlockPivotRowOfMem hp) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2ResidualBlockPivotRowOfMem hp)
                (case2ResidualBlockPivotColOfMem hp)
                (case2SourceSelectedNormalizedMatrixOfMem hp residual) -
              pivotFirstX
                  (case2ResidualBlockPivotRowOfMem hp)
                  (case2ResidualBlockPivotColOfMem hp)
                  (case2SourceSelectedNormalizedMatrixOfMem hp residual) *
                pivotFirstY
                  (case2ResidualBlockPivotRowOfMem hp)
                  (case2ResidualBlockPivotColOfMem hp)
                  (case2SourceSelectedNormalizedMatrixOfMem hp residual))) *
          case2SourceSelectedTransportedFollowingFactorOfMem hp residual C := by
  simpa [case2SourceSelectedNormalizedMatrixOfMem,
    case2SourceSelectedSubstitutionMatrixOfMem,
    case2SourceSelectedFollowingFactorOfMem,
    case2SourceSelectedTransportedFollowingFactorOfMem,
    case2SourceResidualBlock, case2SourceFollowingFactor] using
    hnew.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData
      hpost hgap
      (case2ResidualBlockPivotRowOfMem hp)
      (case2ResidualBlockPivotColOfMem hp)
      (case2SourceResidualBlock residual)
      (case2SourceFollowingFactor C)

end CorrectedCase2NewLabelCertificate

/-- Supplied boundary for a Case 2 source-selected residual-block pivot.

The pivot `p` is supplied as an entry of the finite residual-block center.
This package glues together the already separated finite obligations:

* the source continuation bounds that give the corrected new-label certificate;
* the pre-state exponent certificates, level/least-value bridge, and Case 2 gap;
* the supplied recurrence and corrected exponent post-data for the `J`-advance;
* the supplied finite chart-family regularity boundary for the chosen center.

It deliberately does not construct an affine blow-up atlas, prove coverage,
claim that Aoyagi displays non-top-left Case 2 charts, produce post-data from
coordinates, compute Jacobians, prove normal crossings, or perform RLCT
extraction. -/
structure Case2SourceSelectedSuppliedChartFamilyBoundary
    (R : Type*) [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ) (p : ℕ × ℕ)
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ)
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (u : R)
    (ChartRegular : ℕ × ℕ → Prop)
    (TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop) : Prop where
  stage_pos : 1 ≤ S
  stage_le : S ≤ L
  continuation : J + 1 ≤ prefixMinNat n (S + 1)
  pivot_mem : p ∈ case2ResidualBlockPivotEntries n S J
  exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue
  levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue
  leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue
  recurrencePost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u
  exponentPost :
    Case2CorrectedExponentPostData
      (L := L) (n := n) (S := S) (J := J)
      t t' numerator numerator' leastValue leastValue'
  chartFamily :
    Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular

namespace Case2SourceSelectedSuppliedChartFamilyBoundary

/-- The source continuation bounds produce the corrected Case 2 new-label
certificate used by the finite exponent and recurrence APIs. -/
theorem correctedNewLabel
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    CorrectedCase2NewLabelCertificate L n S J :=
  correctedCase2NewLabelCertificate_of_prefixBound
    L n data.stage_pos data.stage_le data.continuation

/-- The supplied corrected exponent post-data assigns the new label the
corrected numerator expression. -/
theorem numerator_new_eq_correctedNumerator
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    numerator' S (J + 1) = correctedCase2NewLabelNumerator n S J :=
  data.exponentPost.numerator_new_eq_correctedNumerator

/-- Under the source continuation bound, the supplied corrected exponent
post-data assigns the new label the selected residual-block coordinate count. -/
theorem numerator_new_eq_card
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    numerator' S (J + 1) = ((case2ResidualBlockPivotEntries n S J).card : ℤ) :=
  data.exponentPost.numerator_new_eq_card_of_cont data.stage_pos data.continuation

/-- The supplied level/least-value bridge turns the integer Case 2 gap into the
recurrence-state gap needed by the source-selected matrix identity. -/
theorem preCase2Gap
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    pre.case2Gap :=
  IntroducedLabelRecurrenceState.case2Gap_of_leastValueGap
    pre data.levelInv data.leastValueGap

/-- Corrected exponent post-data extends the finite exponent certificate domain
from `(S,J)` to `(S,J+1)`. -/
theorem extendExponentDomain
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' :=
  data.exponentPre.extendDomain_correctedCase2NewLabel_of_postData
    data.correctedNewLabel data.exponentPost

/-- Supplied recurrence post-data and corrected exponent post-data preserve the
level/least-value bridge after the `J`-advance. -/
theorem postLevelInvariants
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    IntroducedLabelLevelInvariants L n S (J + 1) post.level leastValue' :=
  data.recurrencePost.levelInvariants_of_correctedExponentPostData
    data.levelInv data.exponentPost

/-- The corrected least-value successor data preserve the integer Case 2 gap. -/
theorem successorLeastValueGap
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    case2IntroducedLabelLeastValueGap L n S (J + 1) leastValue' :=
  IntroducedLabelRecurrenceState.case2IntroducedLabelLeastValueGap_succ data.leastValueGap
    data.exponentPost.leastValue_old data.exponentPost.leastValue_new

/-- The successor supplied recurrence state has the Case 2 recurrence gap. -/
theorem postCase2Gap
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    post.case2Gap :=
  data.recurrencePost.case2Gap_of_leastValueGap_of_correctedExponentPostData
    data.levelInv data.exponentPost data.leastValueGap

/-- The supplied chart-family boundary gives regularity of the selected pivot
chart. -/
theorem chart_regular_selectedPivot
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    ChartRegular p :=
  data.chartFamily.chart_regular_of_mem data.pivot_mem

/-- The supplied chart-family boundary gives regularity for any residual-block
pivot entry. -/
theorem chart_regular_of_mem
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p q : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hq : q ∈ case2ResidualBlockPivotEntries n S J) :
    ChartRegular q :=
  data.chartFamily.chart_regular_of_mem hq

/-- The supplied chart-family boundary gives transition regularity from the
selected pivot to any other supplied residual-block pivot. -/
theorem transition_regular_selectedPivot_of_mem
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p q : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hq : q ∈ case2ResidualBlockPivotEntries n S J) :
    TransitionRegular p q :=
  data.chartFamily.transition_regular_of_mem data.pivot_mem hq

/-- In the selected-entry chart for the supplied pivot, the finite residual
center ideal pulls back to the principal ideal generated by the selected
variable. -/
theorem selectedPivot_centerIdeal_eq_span_singleton
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) :
    Ideal.span
        {v : R | ∃ q, q ∈ case2ResidualBlockPivotEntries n S J ∧
          selectedEntryChartMap p u residual q = v} =
      Ideal.span ({u} : Set R) :=
  case2_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem
    data.pivot_mem u residual

/-- The source-selected arbitrary-pivot `Q/P` identity available from the
supplied boundary.

This is the existing finite source-selected matrix identity, with the corrected
new-label certificate and pre-state recurrence gap derived from the supplied
source continuation and least-value gap data.  It remains conditional on the
supplied pivot and supplied post-data; it is not chart coverage or a
source-order theorem for non-displayed pivots. -/
theorem sourceSelectedQP
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    ∃ q : pivotComplement (case2ResidualBlockPivotRowOfMem data.pivot_mem) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2ResidualBlockPivotRowOfMem data.pivot_mem)
              (case2ResidualBlockPivotColOfMem data.pivot_mem)
              (case2SourceSelectedNormalizedMatrixOfMem data.pivot_mem residual) i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionMatrixOfMem data.pivot_mem u residual).submatrix
            (pivotFirstIndexEquiv (case2ResidualBlockPivotRowOfMem data.pivot_mem))
            (pivotFirstIndexEquiv (case2ResidualBlockPivotColOfMem data.pivot_mem))) *
          case2SourceSelectedFollowingFactorOfMem data.pivot_mem C =
        (weightedPivotDiagonal
            (post.weight
              (case2ResidualRowLevel n S J
                (case2ResidualBlockPivotRowOfMem data.pivot_mem)))
            (fun i : pivotComplement (case2ResidualBlockPivotRowOfMem data.pivot_mem) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2ResidualBlockPivotRowOfMem data.pivot_mem)
                (case2ResidualBlockPivotColOfMem data.pivot_mem)
                (case2SourceSelectedNormalizedMatrixOfMem data.pivot_mem residual) -
              pivotFirstX
                  (case2ResidualBlockPivotRowOfMem data.pivot_mem)
                  (case2ResidualBlockPivotColOfMem data.pivot_mem)
                  (case2SourceSelectedNormalizedMatrixOfMem data.pivot_mem residual) *
                pivotFirstY
                  (case2ResidualBlockPivotRowOfMem data.pivot_mem)
                  (case2ResidualBlockPivotColOfMem data.pivot_mem)
                  (case2SourceSelectedNormalizedMatrixOfMem data.pivot_mem residual))) *
          case2SourceSelectedTransportedFollowingFactorOfMem data.pivot_mem residual C := by
  exact
    data.correctedNewLabel
      |>.exists_case2SourceSelectedQP_of_recurrenceStateGap_succWeights_of_postData
        data.pivot_mem data.recurrencePost data.preCase2Gap residual C

/-- Source-coordinate selected-pivot Case 2 `Q/P` identity, rewritten in the
source-selected chart-map names.

This is the same finite algebra as `sourceSelectedQP`, with the substituted
and normalised blocks now expressed through the source-coordinate selected
chart map for the supplied pivot.  The pivot is still supplied; this proves no
atlas coverage, non-displayed source formula, or chart-produced post-data. -/
theorem sourceSelectedQP_sourceChartMap
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    let row := case2ResidualBlockPivotRowOfMem data.pivot_mem
    let col := case2ResidualBlockPivotColOfMem data.pivot_mem
    let A := case2SourceSelectedNormalizedBlockOfMem data.pivot_mem residual
    let Csrc := case2SourceSelectedFollowingFactorOfMem data.pivot_mem C
    let Ctr :=
      case2SourceSelectedTransportedFollowingFactorOfMem data.pivot_mem residual C
    ∃ q : pivotComplement row → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2SourceSelectedSubstitutionBlockOfMem data.pivot_mem u residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          Csrc =
        (weightedPivotDiagonal
            (post.weight (case2ResidualRowLevel n S J row))
            (fun i : pivotComplement row ↦ post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A)) *
          Ctr := by
  simpa [case2SourceSelectedNormalizedBlockOfMem_eq_selectedNormalizedMatrixOfMem,
    case2SourceSelectedSubstitutionBlockOfMem_eq_selectedSubstitutionMatrixOfMem]
    using data.sourceSelectedQP residual C

/-- The displayed top-left Case 2 pivot belongs to the finite residual-block
center under the continuation hypotheses carried by the supplied boundary. -/
theorem displayedPivot_mem
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    (J + 1, J + 1) ∈ case2ResidualBlockPivotEntries n S J :=
  case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
    n data.stage_pos data.continuation

/-- The supplied chart-family boundary gives regularity of Aoyagi's displayed
top-left Case 2 pivot. -/
theorem chart_regular_displayedPivot
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    ChartRegular (J + 1, J + 1) :=
  data.chartFamily.chart_regular_of_mem data.displayedPivot_mem

/-- The supplied chart-family boundary gives transition regularity from the
selected pivot to Aoyagi's displayed top-left pivot. -/
theorem transition_regular_selectedPivot_displayedPivot
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    TransitionRegular p (J + 1, J + 1) :=
  data.chartFamily.transition_regular_of_mem data.pivot_mem data.displayedPivot_mem

/-- Concrete recurrence/exponent-update constructor for the supplied
source-selected Case 2 boundary.

The recurrence post-state is the named successor assignment `pre.case2Succ u`,
and the exponent post-data is the corrected selected-label override.  This
still does not assert that a polynomial chart produces these data. -/
theorem of_case2Succ_updateSelected
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ} {p : ℕ × ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hp : p ∈ case2ResidualBlockPivotEntries n S J)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular) :
    Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J p
      t
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      numerator
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      leastValue
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue)
      pre (pre.case2Succ u) u ChartRegular TransitionRegular where
  stage_pos := hS
  stage_le := hSL
  continuation := hcont
  pivot_mem := hp
  exponentPre := exponentPre
  levelInv := levelInv
  leastValueGap := leastValueGap
  recurrencePost := pre.case2Succ_case2SuppliedPostData u
  exponentPost := Case2CorrectedExponentPostData.updateSelected t numerator leastValue
  chartFamily := chartFamily

end Case2SourceSelectedSuppliedChartFamilyBoundary

/-- Displayed top-left Case 2 supplied boundary.

This is the source-displayed specialization of
`Case2SourceSelectedSuppliedChartFamilyBoundary`: the pivot is fixed to
`(J+1,J+1)` and its finite-center membership follows from the continuation
bound.  Recurrence post-data, corrected exponent post-data, and chart-family
regularity are still supplied fields unless a constructor explicitly provides
concrete assignments. -/
structure Case2DisplayedSuppliedChartFamilyBoundary
    (R : Type*) [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (t t' : ℕ → ℕ → ℕ → ℤ)
    (numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ)
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (u : R)
    (ChartRegular : ℕ × ℕ → Prop)
    (TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop) : Prop where
  stage_pos : 1 ≤ S
  stage_le : S ≤ L
  continuation : J + 1 ≤ prefixMinNat n (S + 1)
  exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue
  levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue
  leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue
  recurrencePost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u
  exponentPost :
    Case2CorrectedExponentPostData
      (L := L) (n := n) (S := S) (J := J)
      t t' numerator numerator' leastValue leastValue'
  chartFamily :
    Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular

namespace Case2DisplayedSuppliedChartFamilyBoundary

/-- The displayed top-left pivot is in the Case 2 residual-block center. -/
theorem displayedPivot_mem
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    (J + 1, J + 1) ∈ case2ResidualBlockPivotEntries n S J :=
  case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
    n data.stage_pos data.continuation

/-- A displayed boundary is a source-selected boundary for the displayed
top-left pivot. -/
theorem sourceSelectedBoundary
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    Case2SourceSelectedSuppliedChartFamilyBoundary R L n S J (J + 1, J + 1)
      t t' numerator numerator' leastValue leastValue'
      pre post u ChartRegular TransitionRegular where
  stage_pos := data.stage_pos
  stage_le := data.stage_le
  continuation := data.continuation
  pivot_mem := data.displayedPivot_mem
  exponentPre := data.exponentPre
  levelInv := data.levelInv
  leastValueGap := data.leastValueGap
  recurrencePost := data.recurrencePost
  exponentPost := data.exponentPost
  chartFamily := data.chartFamily

/-- The displayed boundary gives the corrected new-label certificate. -/
theorem correctedNewLabel
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    CorrectedCase2NewLabelCertificate L n S J :=
  data.sourceSelectedBoundary.correctedNewLabel

/-- The displayed boundary's corrected exponent post-data assigns the new
label the corrected numerator expression. -/
theorem numerator_new_eq_correctedNumerator
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    numerator' S (J + 1) = correctedCase2NewLabelNumerator n S J :=
  data.exponentPost.numerator_new_eq_correctedNumerator

/-- Under displayed continuation, the displayed boundary's corrected exponent
post-data assigns the new label the selected residual-block coordinate count. -/
theorem numerator_new_eq_card
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    numerator' S (J + 1) = ((case2ResidualBlockPivotEntries n S J).card : ℤ) :=
  data.exponentPost.numerator_new_eq_card_of_cont data.stage_pos data.continuation

/-- The displayed boundary gives the pre-state recurrence Case 2 gap. -/
theorem preCase2Gap
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    pre.case2Gap :=
  data.sourceSelectedBoundary.preCase2Gap

/-- The displayed boundary extends finite exponent certificates to `(S,J+1)`. -/
theorem extendExponentDomain
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' :=
  data.sourceSelectedBoundary.extendExponentDomain

/-- The displayed boundary preserves the supplied level/least-value bridge
after the Case 2 `J`-advance. -/
theorem postLevelInvariants
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    IntroducedLabelLevelInvariants L n S (J + 1) post.level leastValue' :=
  data.sourceSelectedBoundary.postLevelInvariants

/-- The displayed boundary's corrected least-value successor data preserve the
integer Case 2 gap. -/
theorem successorLeastValueGap
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    case2IntroducedLabelLeastValueGap L n S (J + 1) leastValue' :=
  data.sourceSelectedBoundary.successorLeastValueGap

/-- The displayed boundary's supplied successor recurrence state has the
Case 2 recurrence gap. -/
theorem postCase2Gap
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    post.case2Gap :=
  data.sourceSelectedBoundary.postCase2Gap

/-- The displayed boundary gives supplied chart regularity for the displayed
top-left pivot. -/
theorem chart_regular_displayedPivot
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    ChartRegular (J + 1, J + 1) :=
  data.chartFamily.chart_regular_of_mem data.displayedPivot_mem

/-- The displayed boundary gives finite selected-entry principalization of the
Case 2 residual-block center by the displayed selected variable. -/
theorem displayedPivot_centerIdeal_eq_span_singleton
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) :
    Ideal.span
        {v : R | ∃ q, q ∈ case2ResidualBlockPivotEntries n S J ∧
          selectedEntryChartMap (J + 1, J + 1) u residual q = v} =
      Ideal.span ({u} : Set R) :=
  data.sourceSelectedBoundary.selectedPivot_centerIdeal_eq_span_singleton residual

/-- The displayed boundary exposes the finite frontier branch after its pivot.

This is only branch-domain bookkeeping.  The stopped branches may overlap, and
the result does not assert chart coverage, chart-produced post-data, or a
terminal source model. -/
theorem frontierBranch
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    Case2DisplayedStepBranch n S J :=
  case2DisplayedStepBranch_of_cont data.stage_pos data.continuation

/-- Concrete displayed-boundary constructor using the named recurrence
successor and corrected selected-label exponent updates.

This removes the recurrence/exponent post-data fields by choosing concrete
assignment functions.  It still does not prove these assignments are produced
by an affine chart. -/
theorem of_case2Succ_updateSelected
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular) :
    Case2DisplayedSuppliedChartFamilyBoundary R L n S J
      t
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      numerator
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      leastValue
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue)
      pre (pre.case2Succ u) u ChartRegular TransitionRegular where
  stage_pos := hS
  stage_le := hSL
  continuation := hcont
  exponentPre := exponentPre
  levelInv := levelInv
  leastValueGap := leastValueGap
  recurrencePost := pre.case2Succ_case2SuppliedPostData u
  exponentPost := Case2CorrectedExponentPostData.updateSelected t numerator leastValue
  chartFamily := chartFamily

end Case2DisplayedSuppliedChartFamilyBoundary

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

/-- Under failed next continuation, the displayed Case 2 cleared pivot block has
zero lower-right complement block in pivot-first coordinates.

This is a lower-right vacuity corollary for the already-cleared block.  It is
not a construction of Aoyagi's terminal `D'''_J` branch, the following factor
`C'^(S+1)`, or the `S+1` transition. -/
theorem case2DisplayedClearedBlock_eq_pivotOnly_of_not_next_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    let row := case2DisplayedPivotRow n hS hcont
    let col := case2DisplayedPivotCol n hS hcont
    let A := case2DisplayedNormalizedMatrix n hS hcont residual
    weightedPivotClearedBlock
        (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A) =
      weightedPivotClearedBlock
        (0 : Matrix (pivotComplement row) (pivotComplement col) R) := by
  dsimp
  apply congrArg weightedPivotClearedBlock
  exact case2DisplayedPivotComplement_matrix_eq_zero_of_not_next_cont
    (K := R) hS hcont hstop _

/-- Under failed next continuation, multiplying the displayed cleared Case 2
block by a pivot-first following factor keeps only the top row.

This is the algebraic following-factor consequence of lower-right vacuity.  It
does not construct Aoyagi's `C'^(S+1)` or the `S+1` transition. -/
theorem case2DisplayedClearedBlock_mul_verticalBlock_eq_pivotOnly_of_not_next_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (Ctop : Matrix Unit τ R)
    (Ctail : Matrix (pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    let row := case2DisplayedPivotRow n hS hcont
    let col := case2DisplayedPivotCol n hS hcont
    let A := case2DisplayedNormalizedMatrix n hS hcont residual
    weightedPivotClearedBlock
        (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A) *
        verticalBlock Ctop Ctail =
      verticalBlock Ctop
        (0 : Matrix (pivotComplement row) τ R) := by
  dsimp
  rw [case2DisplayedClearedBlock_eq_pivotOnly_of_not_next_cont
    n hS hcont hstop residual]
  exact weightedPivotClearedBlock_zero_mul_verticalBlock Ctop Ctail

/-- The source-substituted residual block in the displayed Case 2 selected-entry chart. -/
def case2DisplayedSubstitutionMatrix
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  selectedEntrySubstitutionMatrix
    (case2DisplayedPivotRow n hS hcont)
    (case2DisplayedPivotCol n hS hcont) u residual

/-- The displayed Case 2 substituted block is `u` times the normalised residual block. -/
theorem case2DisplayedSubstitutionMatrix_eq_mul_normalized
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    case2DisplayedSubstitutionMatrix n hS hcont u residual =
      fun i j ↦ u * case2DisplayedNormalizedMatrix n hS hcont residual i j :=
  rfl

/-- Displayed Case 2 source-variable transport: the selected variable in the
substituted residual block can be absorbed into the pivot-first row weights. -/
theorem case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) (u : R)
    (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    (diagonal weight * case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
        (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
        (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont)) =
      weightedPivotDiagonal
        (u * weight (case2DisplayedPivotRow n hS hcont))
        (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          u * weight i.1) *
        pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedNormalizedMatrix n hS hcont residual) := by
  simpa [case2DisplayedSubstitutionMatrix, case2DisplayedNormalizedMatrix] using
    pivotFirst_diagonal_mul_selectedEntrySubstitutionMatrix
      (rowPivot := case2DisplayedPivotRow n hS hcont)
      (colPivot := case2DisplayedPivotCol n hS hcont)
      u weight residual

namespace CorrectedCase2NewLabelCertificate

/-- Displayed Case 2 source-variable transport with supplied successor
recurrence weights.  The source-substituted block is still formed with the old
row weights, but the selected variable has been absorbed into the supplied
post-state recurrence weights on the old residual rows.  This is conditional
recurrence bookkeeping, not chart production. -/
theorem case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (u : R)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → post.level s k = pre.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → post.var s k = pre.var s k)
    (hlevel_new : post.level S (J + 1) = J)
    (hvar_new : post.var S (J + 1) = u)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
        case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
        (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
        (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont)) =
      weightedPivotDiagonal
        (post.weight (J + 1))
        (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          post.weight (case2ResidualRowLevel n S J i.1)) *
        pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedNormalizedMatrix n hS hcont residual) := by
  have hupdate :=
    hnew.case2_weight_succ_current_eq_newVar_mul pre post u
      hlevel_old hvar_old hlevel_new hvar_new
  have hpivot :
      u * pre.weight (J + 1) = post.weight (J + 1) :=
    (hupdate (J + 1) le_rfl).symm
  have hpivotResidual :
      u * pre.case2ResidualRowWeight (case2DisplayedPivotRow n hS hcont) =
        post.weight (J + 1) := by
    simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight,
      case2ResidualRowLevel_displayedPivotRow] using hpivot
  have hrows :
      (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        u * pre.case2ResidualRowWeight i.1) =
      (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        post.weight (case2ResidualRowLevel n S J i.1)) := by
    funext i
    exact (by
      simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight] using
        (hupdate (case2ResidualRowLevel n S J i.1)
          (case2ResidualRowLevel_ge n S J i.1)).symm)
  rw [case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst]
  rw [hpivotResidual, hrows]

/-- Displayed Case 2 source-variable transport from a supplied recurrence
post-data package. -/
theorem case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R) :
    (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
        case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
        (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
        (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont)) =
      weightedPivotDiagonal
        (post.weight (J + 1))
        (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          post.weight (case2ResidualRowLevel n S J i.1)) *
        pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedNormalizedMatrix n hS hcont residual) :=
  hnew.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights
    hS hcont pre post u
    hpost.level_old hpost.var_old hpost.level_new hpost.var_new residual

end CorrectedCase2NewLabelCertificate

/-- The following factor for displayed Case 2, reindexed into pivot-first column order. -/
def case2DisplayedFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  pivotFirstFollowingFactor (case2DisplayedPivotCol n hS hcont) C

/-- Restrict a source-coordinate following factor to the residual columns and
then reindex it into the displayed top-left pivot-first column order. -/
def case2DisplayedSourceFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (C : ℕ → τ → R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  case2DisplayedFollowingFactor n hS hcont (case2SourceFollowingFactor C)

/-- Aoyagi Case 1(2)'s displayed normalised source-coordinate block `D_chart`,
restricted to residual rows and actual-width residual columns.  This names the
already normalised block; it is not a chart-construction theorem. -/
def case1DisplayedPaperDchart
    (n : ℕ → ℕ) {S J : ℕ} (_hS : 1 ≤ S)
    (_hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  case2SourceResidualBlock residual

omit [CommRing R] in
/-- The source-coordinate value at Aoyagi's displayed top-left pivot. -/
theorem case1DisplayedPaperDchart_pivot
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    case1DisplayedPaperDchart n hS hcont residual
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont) =
      residual (J + 1, J + 1) := by
  rfl

/-- Aoyagi Case 1(2)'s source block before the displayed `Q/P` operations:
the row strip is reconstructed as `u * D_chart`, while lower residual rows are
left unchanged. -/
def case1DisplayedPaperSourceBlock
    (n : ℕ → ℕ) {S J : ℕ} (J1 : ℕ) (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u
    (case1DisplayedPaperDchart n hS hcont residual)

/-- Aoyagi's displayed Case 1(2) column operation `Q = [1 -y; 0 I]` in
pivot-first source-coordinate form. -/
def case1DisplayedPaperQ
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont))
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) R :=
  pivotQ
    (pivotFirstY
      (case2DisplayedPivotRow n hS hcont)
      (case2DisplayedPivotCol n hS hcont)
      (case1DisplayedPaperDchart n hS hcont residual))

/-- Aoyagi's displayed Case 1(2) inverse column operation `Q⁻¹ = [1 y; 0 I]`
in pivot-first source-coordinate form. -/
def case1DisplayedPaperQinv
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont))
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) R :=
  pivotQinv
    (pivotFirstY
      (case2DisplayedPivotRow n hS hcont)
      (case2DisplayedPivotCol n hS hcont)
      (case1DisplayedPaperDchart n hS hcont residual))

/-- Aoyagi's displayed Case 1(2) block `D'' = D_chart * Q`, after putting the
displayed pivot row and column first. -/
def case1DisplayedPaperDpp
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotRow n hS hcont))
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) R :=
  pivotFirstMatrix
      (case2DisplayedPivotRow n hS hcont)
      (case2DisplayedPivotCol n hS hcont)
      (case1DisplayedPaperDchart n hS hcont residual) *
    case1DisplayedPaperQ n hS hcont residual

/-- Aoyagi's displayed Case 1(2) transported following factor `C' = Q⁻¹ C`,
where `C` is supplied in source-coordinate column form. -/
def case1DisplayedPaperCprime
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  case1DisplayedPaperQinv n hS hcont residual *
    case2DisplayedSourceFollowingFactor n hS hcont C

/-- Aoyagi's displayed Case 1(2) cleared block
`D''' = blockdiag(1, D - x*y)` in pivot-first coordinates. -/
def case1DisplayedPaperDppp
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotRow n hS hcont))
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) R :=
  weightedPivotClearedBlock
    (pivotFirstD
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case1DisplayedPaperDchart n hS hcont residual) -
      pivotFirstX
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case1DisplayedPaperDchart n hS hcont residual) *
        pivotFirstY
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case1DisplayedPaperDchart n hS hcont residual))

/-- If the displayed source-coordinate pivot is normalised to `1`, then the
paper block `D''` is exactly the post-`Q` pivot block. -/
theorem case1DisplayedPaperDpp_eq_pivotPostQBlock
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (hpivot : residual (J + 1, J + 1) = 1) :
    case1DisplayedPaperDpp n hS hcont residual =
      pivotPostQBlock
        (pivotFirstX
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case1DisplayedPaperDchart n hS hcont residual))
        (pivotFirstY
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case1DisplayedPaperDchart n hS hcont residual))
        (pivotFirstD
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case1DisplayedPaperDchart n hS hcont residual)) := by
  have hpivot' :
      case1DisplayedPaperDchart n hS hcont residual
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont) = 1 := by
    simpa [case1DisplayedPaperDchart_pivot] using hpivot
  rw [case1DisplayedPaperDpp, case1DisplayedPaperQ]
  rw [pivotFirstMatrix_eq_pivotPreQBlock _ hpivot']
  rw [pivotPreQBlock_mul_pivotQ]

/-- The paper orientation `C' = Q⁻¹ C`: multiplying `D'' = D_chart * Q` by
`C'` gives the original normalised block times the source following factor. -/
theorem case1DisplayedPaperDpp_mul_Cprime
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    case1DisplayedPaperDpp n hS hcont residual *
        case1DisplayedPaperCprime n hS hcont residual C =
      pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case1DisplayedPaperDchart n hS hcont residual) *
        case2DisplayedSourceFollowingFactor n hS hcont C := by
  rw [case1DisplayedPaperDpp, case1DisplayedPaperCprime,
    case1DisplayedPaperQ, case1DisplayedPaperQinv]
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
    (pivotQ
      (pivotFirstY
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case1DisplayedPaperDchart n hS hcont residual)))
    (pivotQinv
      (pivotFirstY
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case1DisplayedPaperDchart n hS hcont residual)))
    (case2DisplayedSourceFollowingFactor n hS hcont C)]
  rw [pivotQ_mul_pivotQinv]
  simp

namespace Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary

/-- Source-coordinate form of the displayed Case 1(2) source-order identity.

The residual block and following factor are supplied as source-coordinate
functions and then restricted to the residual row/column domains.  This is
only an adapter for the already supplied selected-old/chart-family boundary:
it does not construct the selected-entry chart, raw source pullback, atlas
coverage, regularity, Jacobian data, or transition post-data. -/
theorem sourceOrder_identity_sourceCoordinates
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (hpivot : residual (J + 1, J + 1) = 1) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
          data.pullback.handoff.continuationBound) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                (case2SourceResidualBlock residual) i ()) *
          (diagonal
              (fun i ↦ source.weight (case2ResidualRowLevel n S J i)) *
            case1RowStripSourceMatrix (case1ResidualRowStrip n S J J1) u
              (case2SourceResidualBlock residual)).submatrix
            (pivotFirstIndexEquiv
              (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound))
            (pivotFirstIndexEquiv
              (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound))) *
          case2DisplayedSourceFollowingFactor n data.pullback.handoff.stage_pos
            data.pullback.handoff.continuationBound C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i :
                pivotComplement
                  (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD
                (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                (case2SourceResidualBlock residual) -
              pivotFirstX
                  (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound)
                  (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound)
                  (case2SourceResidualBlock residual) *
                pivotFirstY
                  (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound)
                  (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound)
                  (case2SourceResidualBlock residual)) *
          (pivotQinv
            (pivotFirstY
              (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound)
              (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound)
              (case2SourceResidualBlock residual)) *
            case2DisplayedSourceFollowingFactor n data.pullback.handoff.stage_pos
              data.pullback.handoff.continuationBound C)) := by
  have hpivot' :
      case2SourceResidualBlock residual
          (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
            data.pullback.handoff.continuationBound)
          (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
            data.pullback.handoff.continuationBound) = 1 := by
    simpa [case2SourceResidualBlock, case2DisplayedPivotRow, case2DisplayedPivotCol]
      using hpivot
  simpa [case2DisplayedSourceFollowingFactor] using
    data.sourceOrder_identity
      (case2SourceResidualBlock residual)
      (case2DisplayedFollowingFactor n data.pullback.handoff.stage_pos
        data.pullback.handoff.continuationBound (case2SourceFollowingFactor C))
      hpivot'

/-- Paper-named source-coordinate form of Aoyagi's displayed Case 1(2) `Q/P`
calculation.

The theorem is only a notation/adapter layer over the supplied displayed
source-order identity.  It exposes the paper blocks `D_chart`, `C'`, and
`D'''`; it does not construct the chart, prove coverage or regularity, derive
post-data, compute a Jacobian, prove normal crossings, or extract an RLCT. -/
theorem sourceOrder_identity_sourceCoordinates_paperQP
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {source factoredBase : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    (data :
      Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary R L n S J J1
        s0 k0 t t' numerator numerator' leastValue leastValue'
        source factoredBase post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (hpivot : residual (J + 1, J + 1) = 1) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
          data.pullback.handoff.continuationBound) → R,
      (weightedPivotBlockRowOp q
            (fun i ↦
              pivotFirstX
                (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound)
                (case1DisplayedPaperDchart n data.pullback.handoff.stage_pos
                  data.pullback.handoff.continuationBound residual) i ()) *
          (diagonal
              (fun i ↦ source.weight (case2ResidualRowLevel n S J i)) *
            case1DisplayedPaperSourceBlock n J1 data.pullback.handoff.stage_pos
              data.pullback.handoff.continuationBound u residual).submatrix
            (pivotFirstIndexEquiv
              (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound))
            (pivotFirstIndexEquiv
              (case2DisplayedPivotCol n data.pullback.handoff.stage_pos
                data.pullback.handoff.continuationBound))) *
          case2DisplayedSourceFollowingFactor n data.pullback.handoff.stage_pos
            data.pullback.handoff.continuationBound C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i :
                pivotComplement
                  (case2DisplayedPivotRow n data.pullback.handoff.stage_pos
                    data.pullback.handoff.continuationBound) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          case1DisplayedPaperDppp n data.pullback.handoff.stage_pos
            data.pullback.handoff.continuationBound residual) *
          case1DisplayedPaperCprime n data.pullback.handoff.stage_pos
            data.pullback.handoff.continuationBound residual C := by
  simpa [case1DisplayedPaperDchart, case1DisplayedPaperSourceBlock,
    case1DisplayedPaperDppp, case1DisplayedPaperCprime, case1DisplayedPaperQinv]
    using data.sourceOrder_identity_sourceCoordinates residual C hpivot

end Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary

/-- The displayed Case 2 following factor after Aoyagi's `Q⁻¹ C` update. -/
def case2DisplayedTransportedFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  pivotQinv
      (pivotFirstY
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case2DisplayedNormalizedMatrix n hS hcont residual)) *
    case2DisplayedFollowingFactor n hS hcont C

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

/-- Displayed Case 2 source-variable transport with the following factor included. -/
theorem case2Displayed_diagonal_mul_substitutionMatrix_mul_followingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) (u : R)
    (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ((diagonal weight * case2DisplayedSubstitutionMatrix n hS hcont u residual) *
        C).submatrix
        (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont)) id =
      (weightedPivotDiagonal
          (u * weight (case2DisplayedPivotRow n hS hcont))
          (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
            u * weight i.1) *
        pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedNormalizedMatrix n hS hcont residual)) *
        case2DisplayedFollowingFactor n hS hcont C := by
  rw [← Matrix.submatrix_mul_equiv
    (diagonal weight * case2DisplayedSubstitutionMatrix n hS hcont u residual)
    C
    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))
    id]
  rw [case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst]
  rfl

/-- Source-coordinate selected-entry chart for Aoyagi's displayed top-left
Case 2 pivot.  It names the elementary substitution
`d_(J+1,J+1) = u` and `d_ij = u * residual_ij` off the pivot; the
`n`, `hS`, and `hcont` arguments keep the source chart aligned with the
residual-block domain used below. -/
def case2DisplayedSourceChartMap
    (n : ℕ → ℕ) {S J : ℕ} (_hS : 1 ≤ S)
    (_hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) (p : ℕ × ℕ) : R :=
  selectedEntryChartMap (J + 1, J + 1) u residual p

/-- Source-coordinate normalised residual map for the displayed top-left
Case 2 pivot. -/
def case2DisplayedSourceNormalizedMap
    (n : ℕ → ℕ) {S J : ℕ} (_hS : 1 ≤ S)
    (_hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (p : ℕ × ℕ) : R :=
  selectedEntryNormalizedMap (J + 1, J + 1) residual p

@[simp] theorem case2DisplayedSourceChartMap_pivot
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1) = u := by
  simp [case2DisplayedSourceChartMap]

@[simp] theorem case2DisplayedSourceNormalizedMap_pivot
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    case2DisplayedSourceNormalizedMap n hS hcont residual (J + 1, J + 1) = 1 := by
  simp [case2DisplayedSourceNormalizedMap]

theorem case2DisplayedSourceChartMap_of_ne
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) {p : ℕ × ℕ}
    (hp : p ≠ (J + 1, J + 1)) :
    case2DisplayedSourceChartMap n hS hcont u residual p = u * residual p := by
  exact selectedEntryChartMap_of_ne u residual hp

/-- The source chart map is the selected variable times the normalised source map. -/
theorem case2DisplayedSourceChartMap_eq_mul_normalized
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) (p : ℕ × ℕ) :
    case2DisplayedSourceChartMap n hS hcont u residual p =
      u * case2DisplayedSourceNormalizedMap n hS hcont residual p :=
  rfl

/-- The concrete Case 2 recurrence successor uses the displayed source chart's
pivot coordinate as its new recurrence variable.

This is recurrence bookkeeping tied to the displayed pivot value only; it does
not assert chart-produced exponent data, chart coverage, coordinate regularity,
or a full Case 2 transition. -/
theorem case2DisplayedSourceChartMap_case2Succ_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    IntroducedLabelRecurrenceState.Case2SuppliedPostData pre (pre.case2Succ u)
      (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)) := by
  simpa using pre.case2Succ_case2SuppliedPostData
    (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))

/-- For the concrete Case 2 recurrence successor, Aoyagi's displayed pivot
chart coordinate multiplies every recurrence weight from row `J+1` onward.

The displayed source chart contributes only its pivot value here; no exponent
post-data, Jacobian arithmetic, chart coverage, or transition invariant is
claimed. -/
theorem case2DisplayedSourceChartMap_case2Succ_weight_update
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    ∀ i, J + 1 ≤ i →
      (pre.case2Succ u).weight i =
        case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1) *
          pre.weight i := by
  intro i hi
  have hnew : actualWidthLabel L n S (J + 1) :=
    actualWidthLabel_case2_new L n hS hSL
      (le_trans hcont (prefixMinNat_le_width n (by omega : 1 ≤ S + 1)))
  simpa using
    (pre.case2Succ_case2SuppliedPostData u).weight_succ_current_eq_new_mul_of_ge
      (i := i) hnew hi

/-- Residual-row form of the displayed Case 2 recurrence-weight update. -/
theorem case2DisplayedSourceChartMap_case2Succ_residualRowWeight_update
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R)
    (i : Case2ResidualRowIndex n S J) :
    (pre.case2Succ u).weight (case2ResidualRowLevel n S J i) =
      case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1) *
        pre.case2ResidualRowWeight i := by
  simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight] using
    case2DisplayedSourceChartMap_case2Succ_weight_update
      pre hS hSL hcont u residual (case2ResidualRowLevel n S J i)
      (case2ResidualRowLevel_ge n S J i)

/-- In the displayed source-coordinate Case 2 chart, the selected variable
occurs as a transformed value of the finite residual-block center.  This is
finite chart-map bookkeeping, not chart coverage. -/
theorem case2DisplayedSourceChartMap_value_mem
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    u ∈
      {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        case2DisplayedSourceChartMap n hS hcont u residual p = v} := by
  simpa [case2DisplayedSourceChartMap] using
    case2_displayedPivot_selectedEntryChartMap_value_mem n hS hcont u residual

/-- In the displayed source-coordinate Case 2 chart, every transformed finite
center generator is divisible by the selected variable. -/
theorem case2DisplayedSourceChartMap_center_dvd
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    ∀ p, p ∈ case2ResidualBlockPivotEntries n S J →
      u ∣ case2DisplayedSourceChartMap n hS hcont u residual p := by
  intro p hp
  simpa [case2DisplayedSourceChartMap] using
    (case2_selectedEntryChartMap_center_dvd_of_mem
      (case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont)
      u residual p hp)

/-- In the displayed source-coordinate Case 2 chart, the transformed finite
residual-block center ideal is generated by the selected variable.  This is
finite ideal algebra only, not a chart-production or Jacobian theorem. -/
theorem case2DisplayedSourceChartMap_centerIdeal_eq_span_singleton
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    Ideal.span
        {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
          case2DisplayedSourceChartMap n hS hcont u residual p = v} =
      Ideal.span ({u} : Set R) := by
  simpa [case2DisplayedSourceChartMap] using
    case2_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem
      (case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hcont)
      u residual

omit [CommRing R] in
/-- Equality with the source pair `(J+1,J+1)` is the same as equality with
the displayed pivot in the residual-block subtype product. -/
theorem case2Displayed_source_pair_eq_pivot_iff
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (i : Case2ResidualRowIndex n S J)
    (j : Case2ResidualColIndex n S J) :
    (i.1, j.1) = (J + 1, J + 1) ↔
      (i, j) =
        (case2DisplayedPivotRow n hS hcont,
         case2DisplayedPivotCol n hS hcont) := by
  constructor
  · intro h
    rcases Prod.ext_iff.mp h with ⟨hi, hj⟩
    apply Prod.ext
    · exact Subtype.ext hi
    · exact Subtype.ext hj
  · intro h
    cases h
    rfl

/-- Source-coordinate displayed Case 2 substituted block, restricted to
residual rows and columns. -/
def case2DisplayedSourceSubstitutionBlock
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  fun i j ↦ case2DisplayedSourceChartMap n hS hcont u residual (i.1, j.1)

/-- Source-coordinate displayed Case 2 normalised block, restricted to
residual rows and columns. -/
def case2DisplayedSourceNormalizedBlock
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  fun i j ↦ case2DisplayedSourceNormalizedMap n hS hcont residual (i.1, j.1)

/-- The source-coordinate normalised block agrees with the displayed
block-indexed normalised matrix after restricting source residuals. -/
theorem case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    case2DisplayedSourceNormalizedBlock n hS hcont residual =
      case2DisplayedNormalizedMatrix n hS hcont (case2SourceResidualBlock residual) := by
  ext i j
  by_cases hsrc : (i.1, j.1) = (J + 1, J + 1)
  · have hsub := (case2Displayed_source_pair_eq_pivot_iff n hS hcont i j).1 hsrc
    simp [case2DisplayedSourceNormalizedBlock, case2DisplayedSourceNormalizedMap,
      case2DisplayedNormalizedMatrix, selectedEntryNormalizedMatrix,
      selectedEntryNormalizedMap, hsrc, hsub]
  · have hsub :
        (i, j) ≠
          (case2DisplayedPivotRow n hS hcont,
           case2DisplayedPivotCol n hS hcont) := by
      intro h
      exact hsrc ((case2Displayed_source_pair_eq_pivot_iff n hS hcont i j).2 h)
    simp [case2DisplayedSourceNormalizedBlock, case2DisplayedSourceNormalizedMap,
      case2DisplayedNormalizedMatrix, selectedEntryNormalizedMatrix,
      selectedEntryNormalizedMap, case2SourceResidualBlock, hsrc, hsub]

/-- The source-coordinate substituted block agrees with the displayed
block-indexed selected-entry substitution after restricting source residuals. -/
theorem case2DisplayedSourceSubstitutionBlock_eq_displayedSubstitutionMatrix
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    case2DisplayedSourceSubstitutionBlock n hS hcont u residual =
      case2DisplayedSubstitutionMatrix n hS hcont u (case2SourceResidualBlock residual) := by
  ext i j
  by_cases hsrc : (i.1, j.1) = (J + 1, J + 1)
  · have hsub := (case2Displayed_source_pair_eq_pivot_iff n hS hcont i j).1 hsrc
    simp [case2DisplayedSourceSubstitutionBlock, case2DisplayedSourceChartMap,
      case2DisplayedSubstitutionMatrix, selectedEntrySubstitutionMatrix, selectedEntryChartMap,
      hsrc, hsub]
  · have hsub :
        (i, j) ≠
          (case2DisplayedPivotRow n hS hcont,
           case2DisplayedPivotCol n hS hcont) := by
      intro h
      exact hsrc ((case2Displayed_source_pair_eq_pivot_iff n hS hcont i j).2 h)
    simp [case2DisplayedSourceSubstitutionBlock, case2DisplayedSourceChartMap,
      case2DisplayedSubstitutionMatrix, selectedEntrySubstitutionMatrix, selectedEntryChartMap,
      case2SourceResidualBlock, hsrc, hsub]

/-- The source-coordinate substituted block is the selected variable times
the source-coordinate normalised block. -/
theorem case2DisplayedSourceSubstitutionBlock_eq_mul_normalized
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (residual : ℕ × ℕ → R) :
    case2DisplayedSourceSubstitutionBlock n hS hcont u residual =
      fun i j ↦ u * case2DisplayedSourceNormalizedBlock n hS hcont residual i j :=
  rfl

/-- Source-coordinate displayed Case 2 source-variable transport after
putting the displayed pivot row and column first. -/
theorem case2DisplayedSource_diagonal_mul_substitutionBlock_pivotFirst
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) (u : R)
    (weight : Case2ResidualRowIndex n S J → R)
    (residual : ℕ × ℕ → R) :
    (diagonal weight * case2DisplayedSourceSubstitutionBlock n hS hcont u residual).submatrix
        (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
        (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont)) =
      weightedPivotDiagonal
        (u * weight (case2DisplayedPivotRow n hS hcont))
        (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
          u * weight i.1) *
        pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedSourceNormalizedBlock n hS hcont residual) := by
  rw [case2DisplayedSourceSubstitutionBlock_eq_displayedSubstitutionMatrix]
  rw [case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix]
  exact case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst n hS hcont u weight
    (case2SourceResidualBlock residual)

/-- Multiplying the source-coordinate normalised block by a source following
factor is the existing pivot-first following-factor identity after restriction. -/
theorem case2DisplayedSourceNormalizedBlock_mul_sourceFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    pivotFirstMatrix
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case2DisplayedSourceNormalizedBlock n hS hcont residual) *
      case2DisplayedSourceFollowingFactor n hS hcont C =
    (case2DisplayedSourceNormalizedBlock n hS hcont residual *
      case2SourceFollowingFactor C).submatrix
      (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont)) id := by
  rw [case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix]
  exact case2DisplayedNormalizedMatrix_mul_followingFactor n hS hcont
    (case2SourceResidualBlock residual) (case2SourceFollowingFactor C)

/-- Source-coordinate displayed Case 2 transported following factor
`Q⁻¹ C`, written using the source-coordinate normalised block. -/
def case2DisplayedSourceTransportedFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  pivotQinv
      (pivotFirstY
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case2DisplayedSourceNormalizedBlock n hS hcont residual)) *
    case2DisplayedSourceFollowingFactor n hS hcont C

/-- The source-coordinate transported following factor is the existing
displayed transported following factor after source restriction. -/
theorem case2DisplayedSourceTransportedFollowingFactor_eq_displayedTransportedFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    case2DisplayedSourceTransportedFollowingFactor n hS hcont residual C =
      case2DisplayedTransportedFollowingFactor n hS hcont
        (case2SourceResidualBlock residual) (case2SourceFollowingFactor C) := by
  rw [case2DisplayedSourceTransportedFollowingFactor, case2DisplayedTransportedFollowingFactor,
    case2DisplayedSourceFollowingFactor]
  rw [case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix]

/-- Aoyagi Case 2's displayed normalised source-coordinate block `D_chart`,
restricted to residual rows and actual-width residual columns.  This is only
paper notation for the already normalised displayed chart block. -/
def case2DisplayedPaperDchart
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S J) (Case2ResidualColIndex n S J) R :=
  case2DisplayedSourceNormalizedBlock n hS hcont residual

/-- Aoyagi's displayed Case 2 column operation `Q = [1 -y; 0 I]` in
pivot-first source-coordinate form. -/
def case2DisplayedPaperQ
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont))
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) R :=
  pivotQ
    (pivotFirstY
      (case2DisplayedPivotRow n hS hcont)
      (case2DisplayedPivotCol n hS hcont)
      (case2DisplayedPaperDchart n hS hcont residual))

/-- Aoyagi's displayed Case 2 inverse column operation `Q⁻¹ = [1 y; 0 I]`
in pivot-first source-coordinate form. -/
def case2DisplayedPaperQinv
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont))
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) R :=
  pivotQinv
    (pivotFirstY
      (case2DisplayedPivotRow n hS hcont)
      (case2DisplayedPivotCol n hS hcont)
      (case2DisplayedPaperDchart n hS hcont residual))

/-- Aoyagi's displayed Case 2 block `D'' = D_chart * Q`, after putting the
displayed pivot row and column first. -/
def case2DisplayedPaperDpp
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotRow n hS hcont))
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) R :=
  pivotFirstMatrix
      (case2DisplayedPivotRow n hS hcont)
      (case2DisplayedPivotCol n hS hcont)
      (case2DisplayedPaperDchart n hS hcont residual) *
    case2DisplayedPaperQ n hS hcont residual

/-- Aoyagi's displayed Case 2 transported following factor `C' = Q⁻¹ C`,
where `C` is supplied in source-coordinate column form. -/
def case2DisplayedPaperCprime
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  case2DisplayedPaperQinv n hS hcont residual *
    case2DisplayedSourceFollowingFactor n hS hcont C

/-- Construct the old pivot-first following factor from a displayed Case 2
chart-coordinate following factor `C'`.

This is only the finite coordinate direction `C = Q * C'` in pivot-first
coordinates.  It does not construct a total source-coordinate function
`ℕ → τ → R`, a successor chart family, or a transition invariant. -/
def case2DisplayedPaperConstructedFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  case2DisplayedPaperQ n hS hcont residual * Cprime

/-- Construct a total source-coordinate following factor whose residual-column
restriction, after pivot-first reindexing, is the supplied pivot-first matrix.

Values outside the residual-column range are set to zero.  This is a finite
source-coordinate representative for supplied following-factor data; it is not
chart production, source production of a successor `C'^(S+1)`, recurrence or
exponent post-data, coverage, regularity, Jacobian arithmetic, normal
crossings, or RLCT extraction. -/
noncomputable def case2DisplayedConstructedSourceFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (Csrc : Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    ℕ → τ → R :=
  fun j a =>
    if hj : j ∈ case2ResidualBlockCols n S J then
      Csrc ((pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont)).symm
        ⟨j, hj⟩) a
    else 0

/-- Restricting the constructed source-coordinate following factor to the old
residual columns recovers the supplied pivot-first following factor. -/
theorem case2DisplayedSourceFollowingFactor_constructed
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (Csrc : Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    case2DisplayedSourceFollowingFactor n hS hcont
        (case2DisplayedConstructedSourceFollowingFactor n hS hcont Csrc) =
      Csrc := by
  ext i a
  simp [case2DisplayedSourceFollowingFactor, case2DisplayedFollowingFactor,
    pivotFirstFollowingFactor, case2SourceFollowingFactor,
    case2DisplayedConstructedSourceFollowingFactor]

/-- If the old following factor is constructed as `Q * C'`, then Aoyagi's
displayed inverse operation recovers the chart coordinate `C'`. -/
theorem case2DisplayedPaperCprime_of_constructedFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    case2DisplayedPaperQinv n hS hcont residual *
        case2DisplayedPaperConstructedFollowingFactor n hS hcont residual Cprime =
      Cprime := by
  rw [case2DisplayedPaperConstructedFollowingFactor, case2DisplayedPaperQ,
    case2DisplayedPaperQinv]
  rw [← Matrix.mul_assoc]
  rw [pivotQinv_mul_pivotQ]
  simp

/-- Source-coordinate form of the reverse Case 2 following-factor direction:
if the source following factor is reconstructed from `Q*C'`, Aoyagi's
displayed inverse operation recovers the free pivot-first coordinate `C'`. -/
theorem case2DisplayedPaperCprime_of_constructedSourceFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    case2DisplayedPaperCprime n hS hcont residual
        (case2DisplayedConstructedSourceFollowingFactor n hS hcont
          (case2DisplayedPaperConstructedFollowingFactor n hS hcont residual Cprime)) =
      Cprime := by
  rw [case2DisplayedPaperCprime]
  rw [case2DisplayedSourceFollowingFactor_constructed]
  exact case2DisplayedPaperCprime_of_constructedFollowingFactor
    n hS hcont residual Cprime

/-- Reverse-coordinate form of Aoyagi's displayed Case 2 `Q` operation:
with `C = Q * C'`, multiplying `D'' = D_chart * Q` by `C'` is the same as
multiplying the original normalised block by the constructed old following
factor.

This is finite matrix algebra only.  It is not chart coverage, chart
regularity, post-data production, Jacobian arithmetic, normal crossings, or
RLCT extraction. -/
theorem case2DisplayedPaperDpp_mul_constructedCprime
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    case2DisplayedPaperDpp n hS hcont residual * Cprime =
      pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual) *
        case2DisplayedPaperConstructedFollowingFactor n hS hcont residual Cprime := by
  rw [case2DisplayedPaperDpp, case2DisplayedPaperConstructedFollowingFactor]
  rw [Matrix.mul_assoc]

/-- The top row of Aoyagi's displayed Case 2 transported following factor
`C' = Q⁻¹ C`, in pivot-first coordinates. -/
def case2DisplayedPaperCprimeTop
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix Unit τ R :=
  fun i t ↦ case2DisplayedPaperCprime n hS hcont residual C (Sum.inl i) t

/-- Entrywise expansion of the surviving top row of Aoyagi's transported
following factor `C' = Q⁻¹ C`. -/
theorem case2DisplayedPaperCprimeTop_apply
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (a : τ) :
    case2DisplayedPaperCprimeTop n hS hcont residual C () a =
      C (J + 1) a +
        ∑ j : pivotComplement (case2DisplayedPivotCol n hS hcont),
          case2DisplayedPaperDchart n hS hcont residual
              (case2DisplayedPivotRow n hS hcont) j.1 *
            C j.1.1 a := by
  rw [case2DisplayedPaperCprimeTop, case2DisplayedPaperCprime,
    case2DisplayedPaperQinv]
  rw [pivotQinv_mul_top_apply]
  change
    C (case2DisplayedPivotCol n hS hcont).1 a +
        ∑ j : pivotComplement (case2DisplayedPivotCol n hS hcont),
          case2DisplayedPaperDchart n hS hcont residual
              (case2DisplayedPivotRow n hS hcont) j.1 *
            C j.1.1 a =
      C (J + 1) a +
        ∑ j : pivotComplement (case2DisplayedPivotCol n hS hcont),
          case2DisplayedPaperDchart n hS hcont residual
              (case2DisplayedPivotRow n hS hcont) j.1 *
            C j.1.1 a
  simp [case2DisplayedPivotCol]

/-- Under actual next-width exhaustion, the transported top row `Q⁻¹ C` is
the original source row `J+1`.

This is only the column-exhausted subcase: the post-pivot column complement is
empty, so the finite correction sum in `case2DisplayedPaperCprimeTop_apply`
vanishes. -/
theorem case2DisplayedPaperCprimeTop_apply_of_width_next_eq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (a : τ) :
    case2DisplayedPaperCprimeTop n hS hcont residual C () a =
      C (J + 1) a := by
  rw [case2DisplayedPaperCprimeTop_apply]
  haveI : IsEmpty (pivotComplement (case2DisplayedPivotCol n hS hcont)) :=
    case2DisplayedPivotColComplement_isEmpty_of_width_next_eq hS hcont hwidth
  simp

/-- Matrix-valued form of
`case2DisplayedPaperCprimeTop_apply_of_width_next_eq`. -/
theorem case2DisplayedPaperCprimeTop_eq_sourceRow_of_width_next_eq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    case2DisplayedPaperCprimeTop n hS hcont residual C =
      fun _ a ↦ C (J + 1) a := by
  ext i a
  cases i
  exact case2DisplayedPaperCprimeTop_apply_of_width_next_eq
    n hS hcont hwidth residual C a

/-- The lower rows of Aoyagi's displayed Case 2 transported following factor
`C' = Q⁻¹ C`, in pivot-first coordinates. -/
def case2DisplayedPaperCprimeTail
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  fun i t ↦ case2DisplayedPaperCprime n hS hcont residual C (Sum.inr i) t

/-- The lower rows of Aoyagi's transported following factor `C' = Q⁻¹ C`
are the corresponding lower rows of the original following factor. -/
theorem case2DisplayedPaperCprimeTail_apply
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (j : pivotComplement (case2DisplayedPivotCol n hS hcont)) (a : τ) :
    case2DisplayedPaperCprimeTail n hS hcont residual C j a = C j.1.1 a := by
  rw [case2DisplayedPaperCprimeTail, case2DisplayedPaperCprime,
    case2DisplayedPaperQinv]
  rw [pivotQinv_mul_tail_apply]
  rfl

theorem case2DisplayedPaperCprime_eq_verticalBlock
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    case2DisplayedPaperCprime n hS hcont residual C =
      verticalBlock
        (case2DisplayedPaperCprimeTop n hS hcont residual C)
        (case2DisplayedPaperCprimeTail n hS hcont residual C) := by
  ext i t
  rcases i with i | i <;> rfl

/-- The top row of an arbitrary pivot-first displayed Case 2 chart-coordinate
following factor `C'`. -/
def case2DisplayedFreeCprimeTop
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    Matrix Unit τ R :=
  fun i t ↦ Cprime (Sum.inl i) t

/-- The lower rows of an arbitrary pivot-first displayed Case 2
chart-coordinate following factor `C'`. -/
def case2DisplayedFreeCprimeTail
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    Matrix (pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R :=
  fun i t ↦ Cprime (Sum.inr i) t

omit [CommRing R] in
/-- Any arbitrary pivot-first displayed Case 2 `C'` splits into its top row
and lower-row tail. -/
theorem case2DisplayedFreeCprime_eq_verticalBlock
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    Cprime =
      verticalBlock
        (case2DisplayedFreeCprimeTop n hS hcont Cprime)
        (case2DisplayedFreeCprimeTail n hS hcont Cprime) := by
  ext i t
  rcases i with i | i <;> rfl

/-- The displayed Case 2 lower-right cleared block, reindexed onto the next
same-stage residual row/column domains `(S,J+1)`.

This is the candidate lower-right residual block for the continuing branch as
supplied finite data.  It does not assert chart production, recurrence
post-data, or a transition invariant. -/
noncomputable def case2DisplayedPostPivotResidualBlock
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix (Case2ResidualRowIndex n S (J + 1))
      (Case2ResidualColIndex n S (J + 1)) R :=
  (pivotFirstD
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case2DisplayedPaperDchart n hS hcont residual) -
      pivotFirstX
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual) *
        pivotFirstY
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual)).submatrix
    (case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm
    (case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont).symm

/-- The displayed Case 2 transported following-factor tail, reindexed onto the
next same-stage residual column domain `(S,J+1)`.

This is supplied following-product data for the continuing branch; it is the
tail of `C' = Q^-1 C`, not the original following factor. -/
noncomputable def case2DisplayedPostPivotFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (Case2ResidualColIndex n S (J + 1)) τ R :=
  (case2DisplayedPaperCprimeTail n hS hcont residual C).submatrix
    (case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont).symm id

/-- The tail of an arbitrary pivot-first displayed Case 2 `C'`, reindexed
onto the next same-stage residual column domain `(S,J+1)`.

This is free chart-coordinate following-factor data for the continuing branch.
It does not assert that the arbitrary `C'` was produced from a total
source-coordinate following factor. -/
noncomputable def case2DisplayedPostPivotFreeFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    Matrix (Case2ResidualColIndex n S (J + 1)) τ R :=
  (case2DisplayedFreeCprimeTail n hS hcont Cprime).submatrix
    (case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont).symm id

/-- The reindexed post-pivot following-factor candidate is the original source
following factor restricted to the next same-stage residual columns.  This is
only the lower-row identity for `Q⁻¹ C`, not a full transition theorem. -/
theorem case2DisplayedPostPivotFollowingFactor_eq_sourceFollowingFactor_succ
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    case2DisplayedPostPivotFollowingFactor n hS hcont residual C =
      case2SourceFollowingFactor (n := n) (S := S) (J := J + 1) C := by
  ext j a
  rw [case2DisplayedPostPivotFollowingFactor]
  change
    case2DisplayedPaperCprimeTail n hS hcont residual C
        ((case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont).symm j) a =
      case2SourceFollowingFactor C j a
  rw [case2DisplayedPaperCprimeTail_apply]
  simp [case2SourceFollowingFactor]

/-- The next same-stage residual center is nonempty under the continuing
Case 2 bound.  This only records the branch condition for the supplied
post-pivot data. -/
theorem case2DisplayedPostPivotResidualBlock_nonempty_of_next
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1)) :
    (case2ResidualBlockPivotEntries n S (J + 1)).Nonempty :=
  (case2ResidualBlockPivotEntries_succ_nonempty_iff_next_cont n hS).2 hnext

/-- Aoyagi's displayed Case 2 cleared block
`D''' = blockdiag(1, D - x*y)` in pivot-first coordinates. -/
def case2DisplayedPaperDppp
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    Matrix
      (Unit ⊕ pivotComplement (case2DisplayedPivotRow n hS hcont))
      (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) R :=
  weightedPivotClearedBlock
    (pivotFirstD
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case2DisplayedPaperDchart n hS hcont residual) -
      pivotFirstX
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual) *
        pivotFirstY
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual))

/-- The lower rows of `D''' * C'`, reindexed to the next same-stage residual
row domain, are the supplied post-pivot residual block times the supplied
post-pivot following-factor tail.

This is finite matrix reindexing and block multiplication only.  It does not
produce chart recurrence/exponent post-data, chart coverage, transition
invariance, Jacobian arithmetic, normal crossings, RLCT extraction, arbitrary
pivot coverage, or the terminal `(S+1,0)` relabel. -/
theorem case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    (case2DisplayedPaperDppp n hS hcont residual *
        case2DisplayedPaperCprime n hS hcont residual C).submatrix
        (fun i ↦
          Sum.inr ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i))
        id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2DisplayedPostPivotFollowingFactor n hS hcont residual C := by
  rw [case2DisplayedPaperCprime_eq_verticalBlock]
  rw [case2DisplayedPaperDppp]
  rw [weightedPivotClearedBlock_mul_verticalBlock]
  change
    (((pivotFirstD
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (case2DisplayedPaperDchart n hS hcont residual) -
          pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedPaperDchart n hS hcont residual) *
            pivotFirstY
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedPaperDchart n hS hcont residual)) *
        case2DisplayedPaperCprimeTail n hS hcont residual C).submatrix
        (case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2DisplayedPostPivotFollowingFactor n hS hcont residual C)
  rw [case2DisplayedPostPivotResidualBlock, case2DisplayedPostPivotFollowingFactor]
  exact
    (Matrix.submatrix_mul_equiv
      (pivotFirstD
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual) -
        pivotFirstX
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (case2DisplayedPaperDchart n hS hcont residual) *
          pivotFirstY
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (case2DisplayedPaperDchart n hS hcont residual))
      (case2DisplayedPaperCprimeTail n hS hcont residual C)
      (case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm
      (case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont).symm
      (Equiv.refl τ)).symm

/-- The lower rows of `D''' * C'`, for an arbitrary free pivot-first `C'`,
reindex to the post-pivot residual block times the reindexed tail of `C'`.

This is finite matrix reindexing and block multiplication only.  It does not
produce a source following factor, chart recurrence/exponent post-data, chart
coverage, transition invariance, Jacobian arithmetic, normal crossings, RLCT
extraction, arbitrary pivot coverage, or the terminal `(S+1,0)` relabel. -/
theorem case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    (case2DisplayedPaperDppp n hS hcont residual * Cprime).submatrix
        (fun i ↦
          Sum.inr ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i))
        id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime := by
  rw [show Cprime =
      verticalBlock
        (case2DisplayedFreeCprimeTop n hS hcont Cprime)
        (case2DisplayedFreeCprimeTail n hS hcont Cprime) from
    case2DisplayedFreeCprime_eq_verticalBlock n hS hcont Cprime]
  rw [case2DisplayedPaperDppp]
  rw [weightedPivotClearedBlock_mul_verticalBlock]
  change
    (((pivotFirstD
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (case2DisplayedPaperDchart n hS hcont residual) -
          pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedPaperDchart n hS hcont residual) *
            pivotFirstY
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedPaperDchart n hS hcont residual)) *
        case2DisplayedFreeCprimeTail n hS hcont Cprime).submatrix
        (case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime)
  rw [case2DisplayedPostPivotResidualBlock, case2DisplayedPostPivotFreeFollowingFactor]
  exact
    (Matrix.submatrix_mul_equiv
      (pivotFirstD
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual) -
        pivotFirstX
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (case2DisplayedPaperDchart n hS hcont residual) *
          pivotFirstY
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (case2DisplayedPaperDchart n hS hcont residual))
      (case2DisplayedFreeCprimeTail n hS hcont Cprime)
      (case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm
      (case2DisplayedPivotColComplementEquivResidualColSucc n hS hcont).symm
      (Equiv.refl τ)).symm

/-- Lower rows of the weighted displayed Case 2 product
`weightedPivotDiagonal * D''' * C'` reindex to the lower-row weight diagonal
times the post-pivot free-`C'` product.

This is only the weighted lower-row projection of Aoyagi's displayed right
side.  It does not identify the pivot row, construct a successor following
matrix, produce recurrence/exponent post-data, or prove a transition
invariant. -/
theorem case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R)
    (b : pivotComplement (case2DisplayedPivotRow n hS hcont) → R)
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    ((weightedPivotDiagonal b0 b *
        case2DisplayedPaperDppp n hS hcont residual) * Cprime).submatrix
        (fun i ↦
          Sum.inr ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i))
        id =
      diagonal
          (fun i : Case2ResidualRowIndex n S (J + 1) ↦
            b ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i)) *
        (case2DisplayedPostPivotResidualBlock n hS hcont residual *
          case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime) := by
  rw [weightedPivotDiagonal_mul_lowerRows_reindex
    ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm)
    b0 b
    (case2DisplayedPaperDppp n hS hcont residual)
    Cprime]
  rw [case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct]

/-- The continuing displayed Case 2 lower-row product can be written with the
next same-stage source following factor directly.

This is only the post-pivot tail identity for `C' = Q^-1 C` combined with the
lower-right block product.  It does not produce a successor chart family,
derive recurrence or exponent post-data from coordinates, or prove a
transition invariant. -/
theorem case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct_sourceFollowingFactor
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    (case2DisplayedPaperDppp n hS hcont residual *
        case2DisplayedPaperCprime n hS hcont residual C).submatrix
        (fun i ↦
          Sum.inr ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i))
        id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2SourceFollowingFactor (n := n) (S := S) (J := J + 1) C := by
  rw [case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct]
  rw [case2DisplayedPostPivotFollowingFactor_eq_sourceFollowingFactor_succ]

/-- The paper block `D''` is exactly the post-`Q` pivot block for the
displayed Case 2 source-coordinate chart. -/
theorem case2DisplayedPaperDpp_eq_pivotPostQBlock
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) :
    case2DisplayedPaperDpp n hS hcont residual =
      pivotPostQBlock
        (pivotFirstX
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual))
        (pivotFirstY
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual))
        (pivotFirstD
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual)) := by
  rw [case2DisplayedPaperDpp, case2DisplayedPaperQ]
  rw [pivotFirstMatrix_eq_pivotPreQBlock]
  · rw [pivotPreQBlock_mul_pivotQ]
  · simp [case2DisplayedPaperDchart, case2DisplayedSourceNormalizedBlock,
      case2DisplayedPivotRow, case2DisplayedPivotCol]

/-- The paper orientation `C' = Q⁻¹ C`: multiplying `D'' = D_chart * Q` by
`C'` gives the original normalised block times the source following factor. -/
theorem case2DisplayedPaperDpp_mul_Cprime
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    case2DisplayedPaperDpp n hS hcont residual *
        case2DisplayedPaperCprime n hS hcont residual C =
      pivotFirstMatrix
          (case2DisplayedPivotRow n hS hcont)
          (case2DisplayedPivotCol n hS hcont)
          (case2DisplayedPaperDchart n hS hcont residual) *
        case2DisplayedSourceFollowingFactor n hS hcont C := by
  rw [case2DisplayedPaperDpp, case2DisplayedPaperCprime,
    case2DisplayedPaperQ, case2DisplayedPaperQinv]
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
    (pivotQ
      (pivotFirstY
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case2DisplayedPaperDchart n hS hcont residual)))
    (pivotQinv
      (pivotFirstY
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont)
        (case2DisplayedPaperDchart n hS hcont residual)))
    (case2DisplayedSourceFollowingFactor n hS hcont C)]
  rw [pivotQ_mul_pivotQinv]
  simp

/-- If the next displayed Case 2 continuation fails, the paper-named cleared
block multiplied by `C' = Q⁻¹ C` has the same matrix-entry ideal as the top
row of `C'`.  This drops only the zero lower rows in pivot-first coordinates;
it is not the construction of Aoyagi's next-stage `C'^(S+1)`. -/
theorem matrixEntryIdeal_case2DisplayedPaperDppp_mul_Cprime_eq_top_of_not_next_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    matrixEntryIdeal
        (case2DisplayedPaperDppp n hS hcont residual *
          case2DisplayedPaperCprime n hS hcont residual C) =
      matrixEntryIdeal
        (case2DisplayedPaperCprimeTop n hS hcont residual C) := by
  rw [case2DisplayedPaperCprime_eq_verticalBlock]
  rw [case2DisplayedPaperDppp, case2DisplayedPaperDchart]
  rw [case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix]
  rw [case2DisplayedClearedBlock_mul_verticalBlock_eq_pivotOnly_of_not_next_cont
    n hS hcont hstop (case2SourceResidualBlock residual)]
  simpa [verticalBlock] using
    (matrixEntryIdeal_sumElim_zero_bottom
      (case2DisplayedPaperCprimeTop n hS hcont residual C))

/-- Stacking unchanged old top rows over the stopped displayed Case 2 terminal
block preserves the zero-row absorption entry ideal.

This is the source-order-shaped finite algebra behind keeping old top rows and
dropping the zero lower rows after `D''' * C'`.  It does not identify the right
hand side with Aoyagi's complete next-stage `C'^(S+1)` data, and it is not the
diagonal-weighted full terminal product ideal. -/
theorem matrixEntryIdeal_case2DisplayedPaperTerminalStack_eq_topStack_of_not_next_cont
    {ι : Type*} (Cold : Matrix ι τ R)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    matrixEntryIdeal
        (verticalBlock Cold
          (case2DisplayedPaperDppp n hS hcont residual *
            case2DisplayedPaperCprime n hS hcont residual C)) =
      matrixEntryIdeal
        (verticalBlock Cold
          (case2DisplayedPaperCprimeTop n hS hcont residual C)) := by
  simpa [verticalBlock] using
    matrixEntryIdeal_sumElim_congr_bottom Cold
      (matrixEntryIdeal_case2DisplayedPaperDppp_mul_Cprime_eq_top_of_not_next_cont
        n hS hcont hstop residual C)

/-- Diagonal-weighted version of the stopped displayed Case 2 terminal stack,
with the remaining following product included.

The old top block, old row weights, pivot-row weight, lower residual weights,
and remaining following product are all supplied.  The theorem only proves
that the zero lower residual rows may be dropped from the resulting
matrix-entry ideal; it does not identify the right hand side with Aoyagi's
full terminal product or `C'^(S+1)`. -/
theorem matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack_of_not_next_cont
    {ι υ : Type*} [Fintype ι] [Fintype τ]
    (Wold : Matrix ι ι R) (Cold : Matrix ι τ R)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (b0 : R)
    (b : pivotComplement (case2DisplayedPivotRow n hS hcont) → R)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (F : Matrix τ υ R) :
    matrixEntryIdeal
        ((fromBlocks Wold 0 0 (weightedPivotDiagonal b0 b) *
            verticalBlock Cold
              (case2DisplayedPaperDppp n hS hcont residual *
                case2DisplayedPaperCprime n hS hcont residual C)) * F) =
      matrixEntryIdeal
        (verticalBlock ((Wold * Cold) * F)
          (((show Matrix Unit Unit R from fun _ _ ↦ b0) *
            case2DisplayedPaperCprimeTop n hS hcont residual C) * F)) := by
  have hbottom :
      case2DisplayedPaperDppp n hS hcont residual *
          case2DisplayedPaperCprime n hS hcont residual C =
        verticalBlock
          (case2DisplayedPaperCprimeTop n hS hcont residual C)
          (0 : Matrix (pivotComplement (case2DisplayedPivotRow n hS hcont)) τ R) := by
    rw [case2DisplayedPaperCprime_eq_verticalBlock]
    rw [case2DisplayedPaperDppp, case2DisplayedPaperDchart]
    rw [case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix]
    exact case2DisplayedClearedBlock_mul_verticalBlock_eq_pivotOnly_of_not_next_cont
      n hS hcont hstop (case2SourceResidualBlock residual)
      (case2DisplayedPaperCprimeTop n hS hcont residual C)
      (case2DisplayedPaperCprimeTail n hS hcont residual C)
  rw [hbottom]
  rw [fromBlocks_mul_verticalBlock]
  let C0w : Matrix Unit τ R :=
    (show Matrix Unit Unit R from fun _ _ ↦ b0) *
      case2DisplayedPaperCprimeTop n hS hcont residual C
  have hweighted :
      weightedPivotDiagonal b0 b *
          verticalBlock
            (case2DisplayedPaperCprimeTop n hS hcont residual C)
            (0 : Matrix (pivotComplement (case2DisplayedPivotRow n hS hcont)) τ R) =
        verticalBlock C0w
          (0 : Matrix (pivotComplement (case2DisplayedPivotRow n hS hcont)) τ R) := by
    rw [weightedPivotDiagonal, fromBlocks_mul_verticalBlock]
    simp [C0w]
  rw [hweighted]
  calc
    matrixEntryIdeal ((verticalBlock (Wold * Cold)
          (verticalBlock C0w
            (0 : Matrix (pivotComplement (case2DisplayedPivotRow n hS hcont)) τ R))) * F)
        = matrixEntryIdeal
            ((show Matrix (ι ⊕ Unit) τ R from Sum.elim (Wold * Cold) C0w) * F) := by
          simpa [verticalBlock] using
            matrixEntryIdeal_sumElim_congr_bottom_mul (Wold * Cold) F
              (matrixEntryIdeal_sumElim_zero_bottom_mul C0w F)
    _ = matrixEntryIdeal (verticalBlock ((Wold * Cold) * F) (C0w * F)) := by
          rw [sumElim_mul]
          rfl

/-- Source-displayed Case 2 top-left `Q/P` identity with the following factor reindexed
into pivot-first column coordinates. This is still local finite algebra, not chart coverage. -/
theorem exists_case2DisplayedQP_mul_arbitraryPivotFirstFollowingFactor_of_flat_weights
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

/-- Displayed Case 2 `Q/P` identity with the selected-entry source substitution
factored into the row weights. This is still local finite algebra for the
displayed residual block, not a full source-coordinate chart theorem. -/
theorem exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights
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
          (diagonal weight *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
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
  rcases exists_case2DisplayedQP_mul_arbitraryPivotFirstFollowingFactor_of_flat_weights
      n hS hcont u weight residual C hflat with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst]
  simpa [Matrix.mul_assoc] using hq

/-- Displayed Case 2 source-substitution `Q/P` identity with an arbitrary
pivot-first following factor.

This is the same finite row/column operation as the source-following-factor
version, but the following matrix is already in pivot-first coordinates.  It
does not construct a source-coordinate following function or a chart
transition. -/
theorem exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R)
    (hflat : ∀ i, weight i = weight (case2DisplayedPivotRow n hS hcont)) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          (diagonal weight *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          C =
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
            C) := by
  rcases exists_case2DisplayedQP_mul_of_flat_weights
      n hS hcont u weight residual C hflat with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst]
  simpa [case2DisplayedNormalizedMatrix, Matrix.mul_assoc] using hq

/-- Displayed Case 2 source-substitution `Q/P` identity when the recurrence
factors are trivial over the displayed residual row range.  This proves the
flat row-weight hypothesis from an explicit gap assumption; it is not a full
transition theorem. -/
theorem exists_case2DisplayedQP_mul_sourceSubstitution_of_gap_monomialRec
    (step : ℕ → R) (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hgap : ∀ k, J + 1 ≤ k → k < prefixMinNat n S → step k = 1)
    (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          (diagonal (fun i ↦ monomialRec step (case2ResidualRowLevel n S J i)) *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          case2DisplayedFollowingFactor n hS hcont C =
        (weightedPivotDiagonal
            (u * monomialRec step (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * monomialRec step (case2ResidualRowLevel n S J i.1)) *
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
          case2DisplayedTransportedFollowingFactor n hS hcont residual C := by
  let weight : Case2ResidualRowIndex n S J → R :=
    fun i ↦ monomialRec step (case2ResidualRowLevel n S J i)
  have hflat : ∀ i, weight i = weight (case2DisplayedPivotRow n hS hcont) := by
    intro i
    simp [weight,
      case2ResidualRow_monomialRec_eq_pivot_of_gap step n S J hgap i]
  rcases exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights
      n hS hcont u weight residual C hflat with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  simpa [weight, case2ResidualRowLevel_displayedPivotRow,
    case2DisplayedTransportedFollowingFactor] using hq

/-- Displayed Case 2 source-substitution `Q/P` identity when the monomial
recurrence factors are finite products over labels and the supplied label set
has no labels in the Case 2 gap interval. -/
theorem exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap
    {β : Type*} (labels : Finset β) (level : β → ℕ) (var : β → R)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hgap : ∀ p, p ∈ labels →
      ¬ (J + 1 ≤ level p ∧ level p < prefixMinNat n S))
    (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          (diagonal
              (fun i ↦
                monomialRec (levelProductStep labels level var)
                  (case2ResidualRowLevel n S J i)) *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          case2DisplayedFollowingFactor n hS hcont C =
        (weightedPivotDiagonal
            (u * monomialRec (levelProductStep labels level var) (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * monomialRec (levelProductStep labels level var)
                (case2ResidualRowLevel n S J i.1)) *
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
          case2DisplayedTransportedFollowingFactor n hS hcont residual C := by
  exact exists_case2DisplayedQP_mul_sourceSubstitution_of_gap_monomialRec
    (levelProductStep labels level var) n hS hcont
    (fun k hk hkS ↦ levelProductStep_eq_one_of_gap labels level var hgap hk hkS)
    u residual C

/-- Displayed Case 2 source-substitution `Q/P` identity when the monomial
recurrence factors are products over Lean's finite introduced-label domain and
the introduced labels avoid the Case 2 gap interval. -/
theorem exists_case2DisplayedQP_mul_sourceSubstitution_of_introducedLabelGap
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (level : ℕ → ℕ → ℕ) (var : ℕ → ℕ → R)
    (hgap : ∀ {s k}, introducedLabel L n S J s k →
      ¬ (J + 1 ≤ level s k ∧ level s k < prefixMinNat n S))
    (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          (diagonal
              (fun i ↦
                monomialRec
                  (levelProductStep (introducedLabelFinset L n S J)
                    (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
                    (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2))
                  (case2ResidualRowLevel n S J i)) *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          case2DisplayedFollowingFactor n hS hcont C =
        (weightedPivotDiagonal
            (u * monomialRec
              (levelProductStep (introducedLabelFinset L n S J)
                (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
                (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2)) (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * monomialRec
                (levelProductStep (introducedLabelFinset L n S J)
                  (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
                  (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2))
                (case2ResidualRowLevel n S J i.1)) *
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
          case2DisplayedTransportedFollowingFactor n hS hcont residual C := by
  exact exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap
    (introducedLabelFinset L n S J)
    (fun p : Σ _ : ℕ, ℕ ↦ level p.1 p.2)
    (fun p : Σ _ : ℕ, ℕ ↦ var p.1 p.2) n hS hcont
    (fun p hp ↦ hgap ((mem_introducedLabelFinset.mp hp))) u residual C

/-- Displayed Case 2 source-substitution `Q/P` identity for a packaged
introduced-label recurrence state satisfying the Case 2 gap. -/
theorem exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (state : IntroducedLabelRecurrenceState L n S J R)
    (hgap : state.case2Gap) (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          (diagonal (fun i ↦ state.case2ResidualRowWeight i) *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          case2DisplayedFollowingFactor n hS hcont C =
        (weightedPivotDiagonal
            (u * state.weight (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * state.case2ResidualRowWeight i.1) *
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
          case2DisplayedTransportedFollowingFactor n hS hcont residual C := by
  simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight,
    IntroducedLabelRecurrenceState.step, IntroducedLabelRecurrenceState.weight] using
    exists_case2DisplayedQP_mul_sourceSubstitution_of_introducedLabelGap
      L n hS hcont state.level state.var hgap u residual C

namespace CorrectedCase2NewLabelCertificate

/-- Displayed Case 2 source-substitution `Q/P` identity with supplied successor
recurrence weights.  The left side remains the source substitution with old
row weights; the right-side diagonal is rewritten using a supplied successor
state satisfying the Case 2 recurrence update `b'_i = u * b_i` on the displayed
residual rows.  This is not a proof that the blow-up chart produces the
successor state. -/
theorem exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (post : IntroducedLabelRecurrenceState L n S (J + 1) R)
    (hgap : pre.case2Gap) (u : R)
    (hlevel_old :
      ∀ {s k}, introducedLabel L n S J s k → post.level s k = pre.level s k)
    (hvar_old :
      ∀ {s k}, introducedLabel L n S J s k → post.var s k = pre.var s k)
    (hlevel_new : post.level S (J + 1) = J)
    (hvar_new : post.var S (J + 1) = u)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          case2DisplayedFollowingFactor n hS hcont C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
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
          case2DisplayedTransportedFollowingFactor n hS hcont residual C := by
  rcases exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap
      L n hS hcont pre hgap u residual C with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hupdate :=
    hnew.case2_weight_succ_current_eq_newVar_mul pre post u
      hlevel_old hvar_old hlevel_new hvar_new
  have hpivot :
      u * pre.weight (J + 1) = post.weight (J + 1) :=
    (hupdate (J + 1) le_rfl).symm
  have hrows :
      (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        u * pre.case2ResidualRowWeight i.1) =
      (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        post.weight (case2ResidualRowLevel n S J i.1)) := by
    funext i
    exact (by
      simpa [IntroducedLabelRecurrenceState.case2ResidualRowWeight] using
        (hupdate (case2ResidualRowLevel n S J i.1)
          (case2ResidualRowLevel_ge n S J i.1)).symm)
  rwa [hpivot, hrows] at hq

/-- Displayed Case 2 source-substitution `Q/P` identity from a supplied
recurrence post-data package. -/
theorem exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (hgap : pre.case2Gap)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          case2DisplayedFollowingFactor n hS hcont C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
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
          case2DisplayedTransportedFollowingFactor n hS hcont residual C :=
  hnew.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights
    hS hcont pre post hgap u
    hpost.level_old hpost.var_old hpost.level_new hpost.var_new residual C

/-- Displayed Case 2 source-substitution `Q/P` identity with an arbitrary
pivot-first following factor, from supplied recurrence post-data.

The following factor is not assumed to be source-produced.  This theorem only
uses the supplied recurrence post-data to rewrite the row weights on the
right-hand side. -/
theorem exists_case2DisplayedQP_mul_freeFollowingFactor_of_postData
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    (hnew : CorrectedCase2NewLabelCertificate L n S J)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u)
    (hgap : pre.case2Gap)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
            (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
            (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          C =
        (weightedPivotDiagonal
            (post.weight (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
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
            C) := by
  let weight : Case2ResidualRowIndex n S J → R := fun i ↦ pre.case2ResidualRowWeight i
  have hflat : ∀ i, weight i = weight (case2DisplayedPivotRow n hS hcont) := by
    intro i
    exact pre.case2ResidualRowWeight_eq_displayedPivot_of_case2Gap hS hcont hgap i
  rcases exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights
      n hS hcont u weight residual C hflat with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hupdate :=
    hnew.case2_weight_succ_current_eq_newVar_mul_of_postData hpost
  have hpivot :
      u * pre.weight (J + 1) = post.weight (J + 1) :=
    (hupdate (J + 1) le_rfl).symm
  have hrows :
      (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        u * pre.weight (case2ResidualRowLevel n S J i.1)) =
      (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        post.weight (case2ResidualRowLevel n S J i.1)) := by
    funext i
    exact (by
      simpa using
        (hupdate (case2ResidualRowLevel n S J i.1)
          (case2ResidualRowLevel_ge n S J i.1)).symm)
  simpa [weight, IntroducedLabelRecurrenceState.case2ResidualRowWeight,
    case2ResidualRowLevel_displayedPivotRow, hpivot, hrows] using hq

end CorrectedCase2NewLabelCertificate

namespace Case2DisplayedSuppliedChartFamilyBoundary

open CorrectedCase2NewLabelCertificate

/-- Source-chart-pivot version of the concrete displayed Case 2 supplied
boundary.

The scalar parameter is the displayed source chart value at `(J+1,J+1)`.
The post recurrence state is still the concrete successor for that pivot
value, and the exponent post-data are the corrected selected-label overrides.
This is only supplied-boundary packaging tied to the displayed pivot value; it
does not prove chart coverage, chart-produced exponent data, Jacobian/volume
arithmetic, coordinate regularity, normal crossings, or a full transition. -/
theorem of_sourceChartMap_case2Succ_updateSelected
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular) :
    Case2DisplayedSuppliedChartFamilyBoundary R L n S J
      t
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      numerator
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      leastValue
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue)
      pre
      (pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
      (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))
      ChartRegular TransitionRegular :=
  of_case2Succ_updateSelected pre
    (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))
    hS hSL hcont exponentPre levelInv leastValueGap chartFamily

/-- Source-coordinate displayed top-left Case 2 `Q/P` identity from the
displayed supplied boundary.

This projection uses Aoyagi's displayed pivot `(J+1,J+1)` directly.  The
residual block and following factor are supplied as source-coordinate
functions and then restricted to the residual row/column domains.  This is not
a chart-production theorem. -/
theorem sourceDisplayedQP_sourceCoordinates
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    let row := case2DisplayedPivotRow n data.stage_pos data.continuation
    let col := case2DisplayedPivotCol n data.stage_pos data.continuation
    let A :=
      case2DisplayedNormalizedMatrix n data.stage_pos data.continuation
        (case2SourceResidualBlock residual)
    let Csrc := case2DisplayedSourceFollowingFactor n data.stage_pos data.continuation C
    let Ctr :=
      case2DisplayedTransportedFollowingFactor n data.stage_pos data.continuation
        (case2SourceResidualBlock residual) (case2SourceFollowingFactor C)
    ∃ q : pivotComplement row → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSubstitutionMatrix n data.stage_pos data.continuation u
              (case2SourceResidualBlock residual)).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          Csrc =
        (weightedPivotDiagonal (post.weight (J + 1))
            (fun i : pivotComplement row ↦ post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A)) *
          Ctr := by
  let hnew := data.correctedNewLabel
  simpa [case2DisplayedSourceFollowingFactor] using
    exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData
        hnew data.stage_pos data.continuation data.recurrencePost data.preCase2Gap
        (case2SourceResidualBlock residual) (case2SourceFollowingFactor C)

/-- Source-coordinate displayed top-left Case 2 `Q/P` identity, rewritten in
the source-chart block names.

This is the same finite algebra as `sourceDisplayedQP_sourceCoordinates`;
the substituted block, normalised block, and transported following factor are
now the source-coordinate chart objects.  It still does not prove that the
recurrence or exponent post-data are produced by an affine chart. -/
theorem sourceDisplayedQP_sourceChartMap
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    let row := case2DisplayedPivotRow n data.stage_pos data.continuation
    let col := case2DisplayedPivotCol n data.stage_pos data.continuation
    let A :=
      case2DisplayedSourceNormalizedBlock n data.stage_pos data.continuation residual
    let Csrc := case2DisplayedSourceFollowingFactor n data.stage_pos data.continuation C
    let Ctr :=
      case2DisplayedSourceTransportedFollowingFactor n data.stage_pos data.continuation residual C
    ∃ q : pivotComplement row → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSourceSubstitutionBlock n data.stage_pos data.continuation u
              residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          Csrc =
        (weightedPivotDiagonal (post.weight (J + 1))
            (fun i : pivotComplement row ↦ post.weight (case2ResidualRowLevel n S J i.1)) *
          weightedPivotClearedBlock
            (pivotFirstD row col A - pivotFirstX row col A * pivotFirstY row col A)) *
          Ctr := by
  simpa [case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix,
    case2DisplayedSourceSubstitutionBlock_eq_displayedSubstitutionMatrix,
    case2DisplayedSourceTransportedFollowingFactor_eq_displayedTransportedFollowingFactor]
    using data.sourceDisplayedQP_sourceCoordinates residual C

/-- Paper-named source-coordinate form of Aoyagi's displayed Case 2 `Q/P`
calculation.

This is a notation/adapter layer over the supplied displayed source-chart
identity.  It exposes the paper blocks `D_chart`, `C'`, and `D'''`; it does
not construct the chart, prove coverage or regularity, derive post-data,
compute a Jacobian, prove normal crossings, or extract an RLCT. -/
theorem sourceDisplayedQP_sourceChartMap_paperQP
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    let row := case2DisplayedPivotRow n data.stage_pos data.continuation
    let col := case2DisplayedPivotCol n data.stage_pos data.continuation
    let A := case2DisplayedPaperDchart n data.stage_pos data.continuation residual
    ∃ q : pivotComplement row → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSourceSubstitutionBlock n data.stage_pos data.continuation u
              residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          case2DisplayedSourceFollowingFactor n data.stage_pos data.continuation C =
        (weightedPivotDiagonal (post.weight (J + 1))
            (fun i : pivotComplement row ↦ post.weight (case2ResidualRowLevel n S J i.1)) *
          case2DisplayedPaperDppp n data.stage_pos data.continuation residual) *
          case2DisplayedPaperCprime n data.stage_pos data.continuation residual C := by
  simpa [case2DisplayedPaperDchart, case2DisplayedPaperDppp,
    case2DisplayedPaperCprime, case2DisplayedPaperQinv]
    using data.sourceDisplayedQP_sourceChartMap residual C

/-- Paper-named displayed Case 2 `Q/P` identity with a free chart-coordinate
following factor `Cprime`.

The old pivot-first following factor is constructed as `Q*Cprime`, so the
displayed inverse operation recovers `Cprime` on the right.  This is finite
pivot-first matrix algebra below the supplied-boundary interface; it does not
construct a total source-coordinate following function or chart-produced
post-data. -/
theorem sourceDisplayedQP_constructedCprime_paperQP
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R)
    (Cprime : Matrix
      (Unit ⊕ pivotComplement
        (case2DisplayedPivotCol n data.stage_pos data.continuation)) τ R) :
    let row := case2DisplayedPivotRow n data.stage_pos data.continuation
    let col := case2DisplayedPivotCol n data.stage_pos data.continuation
    let A := case2DisplayedPaperDchart n data.stage_pos data.continuation residual
    ∃ q : pivotComplement row → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSourceSubstitutionBlock n data.stage_pos data.continuation u
              residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          case2DisplayedPaperConstructedFollowingFactor n data.stage_pos
            data.continuation residual Cprime =
        (weightedPivotDiagonal (post.weight (J + 1))
            (fun i : pivotComplement row ↦ post.weight (case2ResidualRowLevel n S J i.1)) *
          case2DisplayedPaperDppp n data.stage_pos data.continuation residual) *
          Cprime := by
  let row := case2DisplayedPivotRow n data.stage_pos data.continuation
  let col := case2DisplayedPivotCol n data.stage_pos data.continuation
  let A := case2DisplayedPaperDchart n data.stage_pos data.continuation residual
  let Csrc :=
    case2DisplayedPaperConstructedFollowingFactor n data.stage_pos data.continuation
      residual Cprime
  let hnew := data.correctedNewLabel
  rcases
      exists_case2DisplayedQP_mul_freeFollowingFactor_of_postData
        hnew data.stage_pos data.continuation data.recurrencePost data.preCase2Gap
        (case2SourceResidualBlock residual) Csrc with
    ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hC :
      pivotQinv
          (pivotFirstY row col
            (case2DisplayedNormalizedMatrix n data.stage_pos data.continuation
              (case2SourceResidualBlock residual))) *
          Csrc =
        Cprime := by
    simpa [row, col, Csrc, case2DisplayedPaperQinv, case2DisplayedPaperDchart,
      case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix] using
      case2DisplayedPaperCprime_of_constructedFollowingFactor
        n data.stage_pos data.continuation residual Cprime
  simpa [row, col, A, Csrc, case2DisplayedPaperDchart, case2DisplayedPaperDppp,
    case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix,
    case2DisplayedSourceSubstitutionBlock_eq_displayedSubstitutionMatrix, hC] using hq

/-- Paper-named displayed Case 2 `Q/P` identity with a free chart-coordinate
following factor, where the old following factor is represented by a total
source-coordinate function.

This packages the source-coordinate lift
`case2DisplayedConstructedSourceFollowingFactor` into the supplied-boundary
`Q/P` calculation.  It still does not produce recurrence or exponent post-data,
construct the successor chart family, prove chart coverage or regularity,
compute Jacobians, prove normal crossings/RLCT, handle arbitrary pivots,
terminal relabeling, or repair the printed Case 2 vector. -/
theorem sourceDisplayedQP_constructedSourceFollowingFactor_paperQP
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R)
    (Cprime : Matrix
      (Unit ⊕ pivotComplement
        (case2DisplayedPivotCol n data.stage_pos data.continuation)) τ R) :
    let row := case2DisplayedPivotRow n data.stage_pos data.continuation
    let col := case2DisplayedPivotCol n data.stage_pos data.continuation
    let A := case2DisplayedPaperDchart n data.stage_pos data.continuation residual
    let C :=
      case2DisplayedConstructedSourceFollowingFactor n data.stage_pos data.continuation
        (case2DisplayedPaperConstructedFollowingFactor n data.stage_pos data.continuation
          residual Cprime)
    ∃ q : pivotComplement row → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSourceSubstitutionBlock n data.stage_pos data.continuation u
              residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          case2DisplayedSourceFollowingFactor n data.stage_pos data.continuation C =
        (weightedPivotDiagonal (post.weight (J + 1))
            (fun i : pivotComplement row ↦ post.weight (case2ResidualRowLevel n S J i.1)) *
          case2DisplayedPaperDppp n data.stage_pos data.continuation residual) *
          Cprime := by
  let Csrc :=
    case2DisplayedPaperConstructedFollowingFactor n data.stage_pos data.continuation
      residual Cprime
  let C :=
    case2DisplayedConstructedSourceFollowingFactor n data.stage_pos data.continuation Csrc
  rcases sourceDisplayedQP_constructedCprime_paperQP data residual Cprime with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hC :
      case2DisplayedSourceFollowingFactor n data.stage_pos data.continuation C = Csrc := by
    dsimp [C, Csrc]
    exact case2DisplayedSourceFollowingFactor_constructed
      n data.stage_pos data.continuation
      (case2DisplayedPaperConstructedFollowingFactor n data.stage_pos data.continuation
        residual Cprime)
  simpa [C, Csrc, hC] using hq

/-- The displayed supplied boundary exposes the continuing-branch lower-row
product of Aoyagi's paper `D''' * C'` as the supplied next same-stage block
product.  This is only a projection to the `(S,J+1)` matrix domains. -/
theorem postPivotNextSameStageProduct
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    (case2DisplayedPaperDppp n data.stage_pos data.continuation residual *
        case2DisplayedPaperCprime n data.stage_pos data.continuation residual C).submatrix
        (fun i ↦
          Sum.inr
            ((case2DisplayedPivotRowComplementEquivResidualRowSucc
              n data.stage_pos data.continuation).symm i))
        id =
      case2DisplayedPostPivotResidualBlock
          n data.stage_pos data.continuation residual *
        case2DisplayedPostPivotFollowingFactor
          n data.stage_pos data.continuation residual C := by
  simpa using
    case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct
      n data.stage_pos data.continuation residual C

/-- The displayed supplied boundary also exposes the continuing-branch
lower-row product with the next same-stage source following factor.

This is a convenience projection combining the post-pivot next-block adapter
with the lower-tail identity for `C' = Q^-1 C`; it is not chart production or
a transition invariant. -/
theorem postPivotNextSameStageProduct_sourceFollowingFactor
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    (case2DisplayedPaperDppp n data.stage_pos data.continuation residual *
        case2DisplayedPaperCprime n data.stage_pos data.continuation residual C).submatrix
        (fun i ↦
          Sum.inr
            ((case2DisplayedPivotRowComplementEquivResidualRowSucc
              n data.stage_pos data.continuation).symm i))
        id =
      case2DisplayedPostPivotResidualBlock
          n data.stage_pos data.continuation residual *
        case2SourceFollowingFactor (n := n) (S := S) (J := J + 1) C := by
  simpa using
    case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct_sourceFollowingFactor
      n data.stage_pos data.continuation residual C

/-- The displayed supplied boundary exposes the continuing-branch lower-row
product of Aoyagi's paper `D''' * C'` for an arbitrary free pivot-first
chart-coordinate following factor `C'`.

This is only a finite matrix projection to the `(S,J+1)` domains.  It does
not assert that the free `C'` is produced by a source-coordinate chart. -/
theorem postPivotFreeCprimeNextSameStageProduct
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement
        (case2DisplayedPivotCol n data.stage_pos data.continuation)) τ R) :
    (case2DisplayedPaperDppp n data.stage_pos data.continuation residual *
        Cprime).submatrix
        (fun i ↦
          Sum.inr
            ((case2DisplayedPivotRowComplementEquivResidualRowSucc
              n data.stage_pos data.continuation).symm i))
        id =
      case2DisplayedPostPivotResidualBlock
          n data.stage_pos data.continuation residual *
        case2DisplayedPostPivotFreeFollowingFactor
          n data.stage_pos data.continuation Cprime := by
  simpa using
    case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
      n data.stage_pos data.continuation residual Cprime

/-- The weighted right side of Aoyagi's displayed Case 2 `Q/P` identity,
projected to lower rows and reindexed to `(S,J+1)`.

The result keeps the successor lower-row diagonal explicit.  It is not an
unweighted lower-row theorem and not a full successor product including the
pivot row. -/
theorem postPivotWeightedFreeCprimeNextSameStageProduct
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement
        (case2DisplayedPivotCol n data.stage_pos data.continuation)) τ R) :
    ((weightedPivotDiagonal (post.weight (J + 1))
        (fun i : pivotComplement
            (case2DisplayedPivotRow n data.stage_pos data.continuation) ↦
          post.weight (case2ResidualRowLevel n S J i.1)) *
      case2DisplayedPaperDppp n data.stage_pos data.continuation residual) *
      Cprime).submatrix
        (fun i ↦
          Sum.inr
            ((case2DisplayedPivotRowComplementEquivResidualRowSucc
              n data.stage_pos data.continuation).symm i))
        id =
      diagonal
          (fun i : Case2ResidualRowIndex n S (J + 1) ↦
            post.weight (case2ResidualRowLevel n S (J + 1) i)) *
        (case2DisplayedPostPivotResidualBlock
            n data.stage_pos data.continuation residual *
          case2DisplayedPostPivotFreeFollowingFactor
            n data.stage_pos data.continuation Cprime) := by
  simpa [case2ResidualRowLevel] using
    case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
      n data.stage_pos data.continuation
      (post.weight (J + 1))
      (fun i : pivotComplement
          (case2DisplayedPivotRow n data.stage_pos data.continuation) ↦
        post.weight (case2ResidualRowLevel n S J i.1))
      residual Cprime

/-- The displayed supplied boundary's continuing-branch next residual center
is nonempty under the explicit next-continuation bound. -/
theorem postPivotResidualBlock_nonempty_of_next
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1)) :
    (case2ResidualBlockPivotEntries n S (J + 1)).Nonempty :=
  case2DisplayedPostPivotResidualBlock_nonempty_of_next n data.stage_pos hnext

/-- Concrete displayed source-chart package for the continuing Case 2 branch.

The source-chart constructor fixes the recurrence successor to the displayed
pivot chart value and fixes the exponent data to the corrected selected-label
overrides.  The post-pivot lower-row product is supplied matrix data over the
same `(S,J+1)` domains; no chart production or transition invariant is
asserted. -/
theorem sourceChartMap_postPivotNextSameStageProduct_withCorrectedPostData
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (C : ℕ → τ → R) :
    (case2DisplayedPaperDppp n hS hcont residual *
        case2DisplayedPaperCprime n hS hcont residual C).submatrix
        (fun i ↦
          Sum.inr
            ((case2DisplayedPivotRowComplementEquivResidualRowSucc
              n hS hcont).symm i))
        id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2DisplayedPostPivotFollowingFactor n hS hcont residual C ∧
    IntroducedLabelExponentCertificates L n S (J + 1)
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelLevelInvariants L n S (J + 1)
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))).level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    case2IntroducedLabelLeastValueGap L n S (J + 1)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    (pre.case2Succ
      (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))).case2Gap := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  exact
    ⟨data.postPivotNextSameStageProduct residual C,
      data.extendExponentDomain,
      data.postLevelInvariants,
      data.successorLeastValueGap,
      data.postCase2Gap⟩

/-- Concrete displayed source-chart package for the continuing Case 2 branch,
with the following-factor tail rewritten as the next same-stage source
following factor.

The source-chart constructor still fixes the recurrence successor by the
displayed pivot chart value and fixes exponent data by corrected selected-label
overrides.  The product identity is a supplied-data compatibility statement
over the `(S,J+1)` domains; no chart production or transition invariant is
asserted. -/
theorem sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (C : ℕ → τ → R) :
    (case2DisplayedPaperDppp n hS hcont residual *
        case2DisplayedPaperCprime n hS hcont residual C).submatrix
        (fun i ↦
          Sum.inr
            ((case2DisplayedPivotRowComplementEquivResidualRowSucc
              n hS hcont).symm i))
        id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2SourceFollowingFactor (n := n) (S := S) (J := J + 1) C ∧
    IntroducedLabelExponentCertificates L n S (J + 1)
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelLevelInvariants L n S (J + 1)
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))).level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    case2IntroducedLabelLeastValueGap L n S (J + 1)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    (pre.case2Succ
      (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))).case2Gap := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  exact
    ⟨data.postPivotNextSameStageProduct_sourceFollowingFactor residual C,
      data.extendExponentDomain,
      data.postLevelInvariants,
      data.successorLeastValueGap,
      data.postCase2Gap⟩

/-- Concrete displayed source-chart package for the continuing Case 2 branch,
with an arbitrary free pivot-first chart-coordinate following factor `C'`.

The source-chart constructor fixes the recurrence successor by the displayed
pivot chart value and fixes exponent data by corrected selected-label
overrides.  The product identity is free finite block algebra over the
`(S,J+1)` domains; no chart atlas, source production of `C'`, or transition
invariant is asserted. -/
theorem sourceChartMap_postPivotFreeCprimeNextSameStageProduct_withCorrectedPostData
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    (case2DisplayedPaperDppp n hS hcont residual * Cprime).submatrix
        (fun i ↦
          Sum.inr
            ((case2DisplayedPivotRowComplementEquivResidualRowSucc
              n hS hcont).symm i))
        id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime ∧
    IntroducedLabelExponentCertificates L n S (J + 1)
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelLevelInvariants L n S (J + 1)
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))).level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    case2IntroducedLabelLeastValueGap L n S (J + 1)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    (pre.case2Succ
      (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))).case2Gap := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  exact
    ⟨data.postPivotFreeCprimeNextSameStageProduct residual Cprime,
      data.extendExponentDomain,
      data.postLevelInvariants,
      data.successorLeastValueGap,
      data.postCase2Gap⟩

/-- Concrete displayed source-chart package combining the constructed-source
`Q/P` identity for a free `C'` with the continuing post-pivot free-`C'`
lower-row product and corrected post-data.

The first conjunct is the weighted source-displayed `Q/P` equality with the
old source following factor reconstructed from `Q*C'`.  The second conjunct is
the separate bare lower-row identity for `D'''*C'`.  Keeping these separate
avoids treating the successor row-weight diagonal as part of the post-pivot
residual block.  This is finite displayed-pivot bookkeeping only; it is not
chart coverage, source production of all `C'`, a successor chart-family
construction, transition invariance, or analytic/RLCT content. -/
theorem sourceChartMap_constructedSourceFreeCprimeLocalProduct_withCorrectedPostData
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    let row := case2DisplayedPivotRow n hS hcont
    let col := case2DisplayedPivotCol n hS hcont
    let A := case2DisplayedPaperDchart n hS hcont residual
    let upivot := case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)
    let post := pre.case2Succ upivot
    let C :=
      case2DisplayedConstructedSourceFollowingFactor n hS hcont
        (case2DisplayedPaperConstructedFollowingFactor n hS hcont residual Cprime)
    ∃ q : pivotComplement row → R,
      (weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSourceSubstitutionBlock n hS hcont upivot residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          case2DisplayedSourceFollowingFactor n hS hcont C =
        (weightedPivotDiagonal (post.weight (J + 1))
            (fun i : pivotComplement row ↦ post.weight (case2ResidualRowLevel n S J i.1)) *
          case2DisplayedPaperDppp n hS hcont residual) * Cprime ∧
      (case2DisplayedPaperDppp n hS hcont residual * Cprime).submatrix
          (fun i ↦
            Sum.inr ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i))
          id =
        case2DisplayedPostPivotResidualBlock n hS hcont residual *
          case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime ∧
      IntroducedLabelExponentCertificates L n S (J + 1)
        (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
        (updateSelectedLabelScalar S (J + 1)
          (((prefixMinNat n S : ℤ) - (J : ℤ)) *
            ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      IntroducedLabelLevelInvariants L n S (J + 1)
        post.level
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      case2IntroducedLabelLeastValueGap L n S (J + 1)
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      post.case2Gap := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  rcases data.sourceDisplayedQP_constructedSourceFollowingFactor_paperQP
      residual Cprime with
    ⟨q, hq⟩
  rcases
      sourceChartMap_postPivotFreeCprimeNextSameStageProduct_withCorrectedPostData
        pre u residual hS hSL hcont exponentPre levelInv leastValueGap
        chartFamily Cprime with
    ⟨hlower, hexp, hlevel, hgap, hcase2⟩
  refine ⟨q, ?_, hlower, hexp, hlevel, hgap, hcase2⟩
  simpa [data] using hq

/-- Concrete displayed source-chart lower-row handoff for the constructed-source
free-`C'` local product.

This projects the `P`-operated source side of the weighted `Q/P` equality to
the lower rows and rewrites the weighted right side by the post-pivot
free-`C'` product. It is finite displayed-pivot algebra only. -/
theorem sourceChartMap_constructedSourceFreeCprimeWeightedNextSameStageProduct_withCorrectedPostData
    {τ R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (Cprime :
      Matrix (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont)) τ R) :
    let row := case2DisplayedPivotRow n hS hcont
    let col := case2DisplayedPivotCol n hS hcont
    let A := case2DisplayedPaperDchart n hS hcont residual
    let upivot := case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)
    let post := pre.case2Succ upivot
    let C :=
      case2DisplayedConstructedSourceFollowingFactor n hS hcont
        (case2DisplayedPaperConstructedFollowingFactor n hS hcont residual Cprime)
    ∃ q : pivotComplement row → R,
      (((weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSourceSubstitutionBlock n hS hcont upivot residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          case2DisplayedSourceFollowingFactor n hS hcont C).submatrix
          (fun i ↦
            Sum.inr ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i))
          id) =
        diagonal
          (fun i : Case2ResidualRowIndex n S (J + 1) ↦
            post.weight (case2ResidualRowLevel n S (J + 1) i)) *
          (case2DisplayedPostPivotResidualBlock n hS hcont residual *
            case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime) ∧
      IntroducedLabelExponentCertificates L n S (J + 1)
        (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
        (updateSelectedLabelScalar S (J + 1)
          (((prefixMinNat n S : ℤ) - (J : ℤ)) *
            ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      IntroducedLabelLevelInvariants L n S (J + 1)
        post.level
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      case2IntroducedLabelLeastValueGap L n S (J + 1)
        (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
      post.case2Gap := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  rcases sourceChartMap_constructedSourceFreeCprimeLocalProduct_withCorrectedPostData
      pre u residual hS hSL hcont exponentPre levelInv leastValueGap chartFamily Cprime with
    ⟨q, hqp, _hlowerBare, hexp, hlevel, hgap, hcase2⟩
  let row := case2DisplayedPivotRow n hS hcont
  let col := case2DisplayedPivotCol n hS hcont
  let A := case2DisplayedPaperDchart n hS hcont residual
  let upivot := case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)
  let post := pre.case2Succ upivot
  let C :=
    case2DisplayedConstructedSourceFollowingFactor n hS hcont
      (case2DisplayedPaperConstructedFollowingFactor n hS hcont residual Cprime)
  let e : Case2ResidualRowIndex n S (J + 1) → Unit ⊕ pivotComplement row :=
    fun i ↦ Sum.inr ((case2DisplayedPivotRowComplementEquivResidualRowSucc n hS hcont).symm i)
  have hproj :
      (((weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
          (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
            case2DisplayedSourceSubstitutionBlock n hS hcont upivot residual).submatrix
            (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
          case2DisplayedSourceFollowingFactor n hS hcont C).submatrix e id) =
        (((weightedPivotDiagonal (post.weight (J + 1))
            (fun i : pivotComplement row ↦
              post.weight (case2ResidualRowLevel n S J i.1)) *
          case2DisplayedPaperDppp n hS hcont residual) *
          Cprime).submatrix e id) := by
    exact congrArg
      (fun M : Matrix (Unit ⊕ pivotComplement row) τ R ↦ M.submatrix e id)
      hqp
  refine ⟨q, ?_, hexp, hlevel, hgap, hcase2⟩
  calc
    (((weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
        (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
          case2DisplayedSourceSubstitutionBlock n hS hcont upivot residual).submatrix
          (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)) *
        case2DisplayedSourceFollowingFactor n hS hcont C).submatrix e id)
        = (((weightedPivotDiagonal (post.weight (J + 1))
              (fun i : pivotComplement row ↦
                post.weight (case2ResidualRowLevel n S J i.1)) *
            case2DisplayedPaperDppp n hS hcont residual) *
            Cprime).submatrix e id) := hproj
    _ = diagonal
          (fun i : Case2ResidualRowIndex n S (J + 1) ↦
            post.weight (case2ResidualRowLevel n S (J + 1) i)) *
          (case2DisplayedPostPivotResidualBlock n hS hcont residual *
            case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime) := by
      simpa [data, row, col, A, upivot, post, e] using
        data.postPivotWeightedFreeCprimeNextSameStageProduct residual Cprime

/-- Source-order terminal weight matrix for the stopped displayed Case 2
candidate.

The old top multiplier is supplied, and the surviving pivot weight is a scalar
`b0`.  This does not prove these are Aoyagi's source-produced next weights. -/
def case2DisplayedPaperTerminalWeight
    {ι R : Type*} [CommRing R] (Wold : Matrix ι ι R) (b0 : R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  fromBlocks Wold 0 0 (show Matrix Unit Unit R from fun _ _ ↦ b0)

/-- Source-order next-following-matrix candidate for the stopped displayed
Case 2 terminal product.

This is the unweighted stack `[Cold; C0]`.  It names the finite matrix shape
suggested by Aoyagi's terminal display, but it does not prove the stack is the
source-produced `C'^(S+1)`. -/
def case2DisplayedPaperTerminalCnext
    {ι τ R : Type*} [CommRing R] (Cold : Matrix ι τ R)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) : Matrix (ι ⊕ Unit) τ R :=
  verticalBlock Cold (case2DisplayedPaperCprimeTop n hS hcont residual C)

/-- Source-row version of the stopped displayed Case 2 terminal next matrix
`C'^(S+1)`.

Rows are indexed by `1,...,J+1`: rows `1,...,J` are the old source rows of the
following matrix, and row `J+1` is the surviving transformed pivot row.  This
is a row packaging of the already defined terminal candidate, not a proof that
the blow-up chart produces the coordinates. -/
def case2DisplayedSourceTerminalCprimeCandidate
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (case2SourceTerminalRowIndex J) τ R :=
  (case2DisplayedPaperTerminalCnext (case2DisplayedSourceOldTopBlock (J := J) C)
    n hS hcont residual C).submatrix (case2SourceTerminalRowEquiv J).symm id

/-- Old source rows of the source-row terminal `C'` candidate are unchanged. -/
theorem case2DisplayedSourceTerminalCprimeCandidate_oldRow
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (i : case2SourceOldTopRowIndex J) (a : τ) :
    case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C
        (case2SourceTerminalRowEquiv J (Sum.inl i)) a =
      C i.1 a := by
  simp [case2DisplayedSourceTerminalCprimeCandidate,
    case2DisplayedPaperTerminalCnext, case2DisplayedSourceOldTopBlock]

/-- The surviving pivot row of the source-row terminal `C'` candidate is the
top row of the transported following factor `Q⁻¹ C`. -/
theorem case2DisplayedSourceTerminalCprimeCandidate_pivotRow
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (a : τ) :
    case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C
        (case2SourceTerminalRowEquiv J (Sum.inr ())) a =
      case2DisplayedPaperCprimeTop n hS hcont residual C () a := by
  simp [case2DisplayedSourceTerminalCprimeCandidate,
    case2DisplayedPaperTerminalCnext]

/-- Original source following rows `1,...,J+1`, indexed by the terminal source
row type.

This matrix is chart-independent.  It becomes the stopped terminal `C'`
candidate only in the actual-width column-exhausted subcase, where the
transported pivot row has no post-pivot column correction. -/
def case2DisplayedSourceTerminalOriginalRows
    {τ R : Type*} {J : ℕ} (C : ℕ → τ → R) :
    Matrix (case2SourceTerminalRowIndex J) τ R :=
  fun i a ↦ C i.1 a

/-- Source terminal rows with the transported pivot row written explicitly.

Rows `1,...,J` are original source rows.  Row `J+1` is the top row of the
transported following factor `Q⁻¹ C`, including any post-pivot column
correction.  This is formula-level terminal data, not source chart
production. -/
def case2DisplayedSourceTerminalTransportedRows
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (case2SourceTerminalRowIndex J) τ R :=
  fun i a ↦
    if i.1 = J + 1 then
      case2DisplayedPaperCprimeTop n hS hcont residual C () a
    else
      C i.1 a

/-- A supplied terminal matrix equal to the old source rows and surviving
pivot row is exactly the source-row terminal `C'` candidate.

This is the handoff point for a later chart-production theorem: the row
equations are supplied here, not proved from coordinates. -/
theorem case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (Cterm : Matrix (case2SourceTerminalRowIndex J) τ R)
    (hold : ∀ i a,
      Cterm (case2SourceTerminalRowEquiv J (Sum.inl i)) a = C i.1 a)
    (hpiv : ∀ a,
      Cterm (case2SourceTerminalRowEquiv J (Sum.inr ())) a =
        case2DisplayedPaperCprimeTop n hS hcont residual C () a) :
    case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C =
      Cterm := by
  ext i a
  let e := case2SourceTerminalRowEquiv J
  have hi : i = e (e.symm i) := by simp [e]
  rw [hi]
  rcases e.symm i with iold | u
  · simp [e, case2DisplayedSourceTerminalCprimeCandidate_oldRow,
      hold iold a]
  · cases u
    simp [e, case2DisplayedSourceTerminalCprimeCandidate_pivotRow, hpiv a]

/-- In the actual-width column-exhausted subcase, the source-row terminal `C'`
candidate is just the original source following rows `1,...,J+1`. -/
theorem case2DisplayedSourceTerminalCprimeCandidate_eq_originalRows_of_width_next_eq
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C =
      case2DisplayedSourceTerminalOriginalRows (J := J) C := by
  refine
    case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow
      n hS hcont residual C
      (case2DisplayedSourceTerminalOriginalRows (J := J) C) ?_ ?_
  · intro i a
    simp [case2DisplayedSourceTerminalOriginalRows]
  · intro a
    simpa [case2DisplayedSourceTerminalOriginalRows] using
      (case2DisplayedPaperCprimeTop_apply_of_width_next_eq
        n hS hcont hwidth residual C a).symm

/-- The source-row terminal `C'` candidate is the explicit transported-row
terminal matrix. -/
theorem case2DisplayedSourceTerminalCprimeCandidate_eq_transportedRows
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C =
      case2DisplayedSourceTerminalTransportedRows n hS hcont residual C := by
  refine
    case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow
      n hS hcont residual C
      (case2DisplayedSourceTerminalTransportedRows n hS hcont residual C) ?_ ?_
  · intro i a
    have hne : i.1 ≠ J + 1 := by
      have hi_le : i.1 ≤ J := (Finset.mem_Icc.mp i.2).2
      omega
    simp [case2DisplayedSourceTerminalTransportedRows, hne]
  · intro a
    simp [case2DisplayedSourceTerminalTransportedRows]

/-- Supplied bridge data identifying a terminal source matrix with the
source-row terminal `C'` candidate.

The bridge records the row equations that a later chart-production theorem
should prove: old rows are unchanged, and the surviving pivot row is the top
row of `Q⁻¹ C`. -/
structure SuppliedTerminalCprimeBridge
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) where
  Cterm : Matrix (case2SourceTerminalRowIndex J) τ R
  oldRow :
    ∀ i a, Cterm (case2SourceTerminalRowEquiv J (Sum.inl i)) a = C i.1 a
  pivotRow :
    ∀ a, Cterm (case2SourceTerminalRowEquiv J (Sum.inr ())) a =
      case2DisplayedPaperCprimeTop n hS hcont residual C () a

namespace SuppliedTerminalCprimeBridge

variable {τ R : Type*} [CommRing R]
variable {n : ℕ → ℕ} {S J : ℕ} {hS : 1 ≤ S}
variable {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
variable {residual : ℕ × ℕ → R} {C : ℕ → τ → R}

/-- A supplied terminal `C'` bridge identifies its matrix with the existing
source-row candidate. -/
theorem cprimeCandidate_eq
    (bridge :
      SuppliedTerminalCprimeBridge n hS hcont residual C) :
    case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C =
      bridge.Cterm :=
  case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow
    n hS hcont residual C bridge.Cterm bridge.oldRow bridge.pivotRow

/-- The explicit transported-row terminal matrix supplies a terminal `C'`
bridge.

This constructor records the formula-level matrix whose last row is the top
row of `Q⁻¹ C`.  It does not identify that row with the original source row
unless a separate actual-width column-exhaustion theorem is available. -/
def of_transportedRows
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    SuppliedTerminalCprimeBridge n hS hcont residual C where
  Cterm := case2DisplayedSourceTerminalTransportedRows n hS hcont residual C
  oldRow := by
    intro i a
    have hne : i.1 ≠ J + 1 := by
      have hi_le : i.1 ≤ J := (Finset.mem_Icc.mp i.2).2
      omega
    simp [case2DisplayedSourceTerminalTransportedRows, hne]
  pivotRow := by
    intro a
    simp [case2DisplayedSourceTerminalTransportedRows]

/-- Actual-width column exhaustion supplies a terminal `C'` bridge whose
terminal matrix is the original source following rows `1,...,J+1`.

This is not a general chart-production theorem.  It uses exactly
`n(S+1)=J+1`, so the top row of `Q⁻¹ C` has no post-pivot column correction. -/
def of_originalRows_width_next_eq
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    SuppliedTerminalCprimeBridge n hS hcont residual C where
  Cterm := case2DisplayedSourceTerminalOriginalRows (J := J) C
  oldRow := by
    intro i a
    simp [case2DisplayedSourceTerminalOriginalRows]
  pivotRow := by
    intro a
    simpa [case2DisplayedSourceTerminalOriginalRows] using
      (case2DisplayedPaperCprimeTop_apply_of_width_next_eq
        n hS hcont hwidth residual C a).symm

end SuppliedTerminalCprimeBridge

/-- The source-row terminal `C'^(S+1)` reindexes back to the stacked
old-top-plus-pivot-row candidate. -/
theorem case2DisplayedSourceTerminalCprimeCandidate_submatrix_terminalRowEquiv
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    (case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C).submatrix
        (case2SourceTerminalRowEquiv J) id =
      case2DisplayedPaperTerminalCnext (case2DisplayedSourceOldTopBlock (J := J) C)
        n hS hcont residual C := by
  ext i t
  simp [case2DisplayedSourceTerminalCprimeCandidate]

/-- Reindexing the source-row terminal `C'^(S+1)` preserves the matrix-entry
ideal of the stacked old-top-plus-pivot-row candidate. -/
theorem matrixEntryIdeal_case2DisplayedSourceTerminalCprimeCandidate_eq_terminalCnext
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    matrixEntryIdeal (case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C) =
      matrixEntryIdeal
        (case2DisplayedPaperTerminalCnext (case2DisplayedSourceOldTopBlock (J := J) C)
          n hS hcont residual C) := by
  exact matrixEntryIdeal_submatrix_equiv
    (case2DisplayedPaperTerminalCnext (case2DisplayedSourceOldTopBlock (J := J) C)
      n hS hcont residual C)
    (case2SourceTerminalRowEquiv J).symm (Equiv.refl τ)

/-- Source-row version of the stopped displayed Case 2 terminal weight. -/
def case2DisplayedSourceTerminalWeight
    {R : Type*} [CommRing R] {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (b0 : R) :
    Matrix (case2SourceTerminalRowIndex J) (case2SourceTerminalRowIndex J) R :=
  (case2DisplayedPaperTerminalWeight Wold b0).submatrix
    (case2SourceTerminalRowEquiv J).symm (case2SourceTerminalRowEquiv J).symm

/-- Source-order candidate for the stopped displayed Case 2 terminal product.

This is `(terminalWeight * terminalCnext) * F`.  It names the finite matrix
shape suggested by Aoyagi's terminal display, but it does not prove that
`terminalCnext` is the source-produced
`C'^(S+1)`. -/
def case2DisplayedPaperTerminalCprimeCandidate
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    (Wold : Matrix ι ι R) (Cold : Matrix ι τ R)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) : Matrix (ι ⊕ Unit) υ R :=
  (case2DisplayedPaperTerminalWeight Wold b0 *
      case2DisplayedPaperTerminalCnext Cold n hS hcont residual C) * F

theorem case2DisplayedPaperTerminalCprimeCandidate_eq_weight_mul_cnext_mul
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    (Wold : Matrix ι ι R) (Cold : Matrix ι τ R)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    case2DisplayedPaperTerminalCprimeCandidate Wold Cold n hS hcont b0 residual C F =
      (case2DisplayedPaperTerminalWeight Wold b0 *
        case2DisplayedPaperTerminalCnext Cold n hS hcont residual C) * F :=
  rfl

/-- Expand the stopped displayed Case 2 source-order candidate into the
weighted old-top row block and weighted surviving pivot row. -/
theorem case2DisplayedPaperTerminalCprimeCandidate_eq_verticalBlock_mul
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    (Wold : Matrix ι ι R) (Cold : Matrix ι τ R)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    case2DisplayedPaperTerminalCprimeCandidate Wold Cold n hS hcont b0 residual C F =
      verticalBlock ((Wold * Cold) * F)
        (((show Matrix Unit Unit R from fun _ _ ↦ b0) *
          case2DisplayedPaperCprimeTop n hS hcont residual C) * F) := by
  rw [case2DisplayedPaperTerminalCprimeCandidate_eq_weight_mul_cnext_mul,
    case2DisplayedPaperTerminalWeight, case2DisplayedPaperTerminalCnext,
    fromBlocks_mul_verticalBlock]
  change
    ((show Matrix (ι ⊕ Unit) τ R from Sum.elim (Wold * Cold)
      ((show Matrix Unit Unit R from fun _ _ ↦ b0) *
        case2DisplayedPaperCprimeTop n hS hcont residual C)) * F) =
      verticalBlock ((Wold * Cold) * F)
        (((show Matrix Unit Unit R from fun _ _ ↦ b0) *
          case2DisplayedPaperCprimeTop n hS hcont residual C) * F)
  rw [sumElim_mul]
  rfl

/-- Source-row version of the stopped displayed Case 2 terminal product
candidate, obtained by row-reindexing the already defined stacked candidate. -/
def case2DisplayedSourceTerminalProductReindexedCandidate
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    Matrix (case2SourceTerminalRowIndex J) υ R :=
  (case2DisplayedPaperTerminalCprimeCandidate Wold
    (case2DisplayedSourceOldTopBlock (J := J) C)
    n hS hcont b0 residual C F).submatrix
    (case2SourceTerminalRowEquiv J).symm id

/-- The source-row terminal product candidate unfolds to the row reindexing of
the stacked stopped terminal candidate. -/
theorem case2DisplayedSourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate_submatrix
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    case2DisplayedSourceTerminalProductReindexedCandidate Wold n hS hcont b0 residual C F =
      (case2DisplayedPaperTerminalCprimeCandidate Wold
        (case2DisplayedSourceOldTopBlock (J := J) C)
        n hS hcont b0 residual C F).submatrix
        (case2SourceTerminalRowEquiv J).symm id :=
  rfl

/-- The source-row terminal product candidate is the product of the separately
named source-row terminal weight and source-row terminal next-factor candidate,
followed by the supplied suffix. -/
theorem case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    case2DisplayedSourceTerminalProductReindexedCandidate Wold n hS hcont b0 residual C F =
      (case2DisplayedSourceTerminalWeight Wold b0 *
        case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C) * F := by
  rw [case2DisplayedSourceTerminalProductReindexedCandidate,
    case2DisplayedPaperTerminalCprimeCandidate, case2DisplayedSourceTerminalWeight,
    case2DisplayedSourceTerminalCprimeCandidate]
  rw [← Matrix.submatrix_mul_equiv
    (case2DisplayedPaperTerminalWeight Wold b0 *
      case2DisplayedPaperTerminalCnext (case2DisplayedSourceOldTopBlock (J := J) C)
        n hS hcont residual C)
    F
    (case2SourceTerminalRowEquiv J).symm
    (Equiv.refl τ)
    (id : υ → υ)]
  rw [← Matrix.submatrix_mul_equiv
    (case2DisplayedPaperTerminalWeight Wold b0)
    (case2DisplayedPaperTerminalCnext (case2DisplayedSourceOldTopBlock (J := J) C)
      n hS hcont residual C)
    (case2SourceTerminalRowEquiv J).symm
    (case2SourceTerminalRowEquiv J).symm
    (Equiv.refl τ)]
  simp

/-- If a supplied terminal source matrix has the old source rows and surviving
pivot row, then the source-row terminal product candidate rewrites to that
supplied matrix.

This theorem does not prove that such a matrix is chart-produced; it records
the exact row equations needed for that later handoff. -/
theorem case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_suppliedCterm_mul
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R)
    (Cterm : Matrix (case2SourceTerminalRowIndex J) τ R)
    (hold : ∀ i a,
      Cterm (case2SourceTerminalRowEquiv J (Sum.inl i)) a = C i.1 a)
    (hpiv : ∀ a,
      Cterm (case2SourceTerminalRowEquiv J (Sum.inr ())) a =
        case2DisplayedPaperCprimeTop n hS hcont residual C () a) :
    case2DisplayedSourceTerminalProductReindexedCandidate Wold n hS hcont
        b0 residual C F =
      (case2DisplayedSourceTerminalWeight Wold b0 * Cterm) * F := by
  rw [case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul]
  rw [case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow
    n hS hcont residual C Cterm hold hpiv]

namespace SuppliedTerminalCprimeBridge

variable {τ υ R : Type*} [CommRing R] [Fintype τ]
variable {n : ℕ → ℕ} {S J : ℕ} {hS : 1 ≤ S}
variable {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
variable {residual : ℕ × ℕ → R} {C : ℕ → τ → R}

/-- Product rewrite supplied by a terminal `C'` bridge. -/
theorem terminalProduct_eq_weight_mul_Cterm_mul
    (bridge :
      SuppliedTerminalCprimeBridge n hS hcont residual C)
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (b0 : R) (F : Matrix τ υ R) :
    case2DisplayedSourceTerminalProductReindexedCandidate Wold n hS hcont
        b0 residual C F =
      (case2DisplayedSourceTerminalWeight Wold b0 * bridge.Cterm) * F :=
  case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_suppliedCterm_mul
    Wold n hS hcont b0 residual C F bridge.Cterm bridge.oldRow bridge.pivotRow

end SuppliedTerminalCprimeBridge

/-- Terminal-prefix-row version of the stopped displayed Case 2 source terminal
weight candidate.  This only reindexes the already named source-row terminal
weight along `1..J+1 = 1..M(S+1)`. -/
def case2DisplayedSourceTerminalWeightPrefixCandidate
    {R : Type*} [CommRing R] {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ}
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (b0 : R) :
    Matrix (case2SourceTerminalPrefixRowIndex n S)
      (case2SourceTerminalPrefixRowIndex n S) R :=
  (case2DisplayedSourceTerminalWeight Wold b0).submatrix
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm

/-- Terminal-prefix-row version of the stopped displayed Case 2 source
`C'^(S+1)` candidate.  This is still only a reindexing of the candidate, not
chart production. -/
def case2DisplayedSourceTerminalCprimePrefixCandidate
    {τ R : Type*} [CommRing R]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) :
    Matrix (case2SourceTerminalPrefixRowIndex n S) τ R :=
  (case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C).submatrix
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm id

namespace SuppliedTerminalCprimeBridge

variable {τ R : Type*} [CommRing R]
variable {n : ℕ → ℕ} {S J : ℕ} {hS : 1 ≤ S}
variable {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
variable {residual : ℕ × ℕ → R} {C : ℕ → τ → R}

/-- Terminal-prefix-row `C'` rewrite supplied by a terminal `C'` bridge. -/
theorem cprimePrefixCandidate_eq
    (bridge :
      SuppliedTerminalCprimeBridge n hS hcont residual C)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1)) :
    case2DisplayedSourceTerminalCprimePrefixCandidate n hS hcont hstop
        residual C =
      bridge.Cterm.submatrix
        (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm id := by
  rw [case2DisplayedSourceTerminalCprimePrefixCandidate, bridge.cprimeCandidate_eq]

end SuppliedTerminalCprimeBridge

/-- Terminal-prefix-row version of the stopped displayed Case 2 source terminal
product candidate. -/
def case2DisplayedSourceTerminalProductPrefixCandidate
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    Matrix (case2SourceTerminalPrefixRowIndex n S) υ R :=
  (case2DisplayedSourceTerminalProductReindexedCandidate Wold n hS hcont b0
    residual C F).submatrix
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm id

/-- The terminal-prefix-row product candidate is the product of the reindexed
terminal-prefix weight and terminal-prefix `C'` candidate, followed by the
supplied suffix. -/
theorem case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_cprimePrefixCandidate_mul
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    case2DisplayedSourceTerminalProductPrefixCandidate Wold n hS hcont hstop
        b0 residual C F =
      (case2DisplayedSourceTerminalWeightPrefixCandidate Wold n hcont hstop b0 *
        case2DisplayedSourceTerminalCprimePrefixCandidate n hS hcont hstop residual C) *
        F := by
  rw [case2DisplayedSourceTerminalProductPrefixCandidate,
    case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul,
    case2DisplayedSourceTerminalWeightPrefixCandidate,
    case2DisplayedSourceTerminalCprimePrefixCandidate]
  rw [← Matrix.submatrix_mul_equiv
    (case2DisplayedSourceTerminalWeight Wold b0 *
      case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C)
    F
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm
    (Equiv.refl τ)
    (id : υ → υ)]
  rw [← Matrix.submatrix_mul_equiv
    (case2DisplayedSourceTerminalWeight Wold b0)
    (case2DisplayedSourceTerminalCprimeCandidate n hS hcont residual C)
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm
    (Equiv.refl τ)]
  simp

namespace SuppliedTerminalCprimeBridge

variable {τ υ R : Type*} [CommRing R] [Fintype τ]
variable {n : ℕ → ℕ} {S J : ℕ} {hS : 1 ≤ S}
variable {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
variable {residual : ℕ × ℕ → R} {C : ℕ → τ → R}

/-- Terminal-prefix-row product rewrite supplied by a terminal `C'` bridge. -/
theorem terminalPrefixProduct_eq_weight_mul_CtermPrefix_mul
    (bridge :
      SuppliedTerminalCprimeBridge n hS hcont residual C)
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (b0 : R) (F : Matrix τ υ R) :
    case2DisplayedSourceTerminalProductPrefixCandidate Wold n hS hcont hstop
        b0 residual C F =
      (case2DisplayedSourceTerminalWeightPrefixCandidate Wold n hcont hstop b0 *
        bridge.Cterm.submatrix
          (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm id) *
        F := by
  rw [case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_cprimePrefixCandidate_mul]
  rw [case2DisplayedSourceTerminalCprimePrefixCandidate, bridge.cprimeCandidate_eq]

end SuppliedTerminalCprimeBridge

/-- Reindexing the stopped source-row product candidate onto the terminal
prefix row range preserves its matrix-entry ideal. -/
theorem matrixEntryIdeal_sourceTerminalProductPrefixCandidate_eq_sourceTerminalProduct
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    matrixEntryIdeal
        (case2DisplayedSourceTerminalProductPrefixCandidate Wold n hS hcont
          hstop b0 residual C F) =
      matrixEntryIdeal
        (case2DisplayedSourceTerminalProductReindexedCandidate Wold n hS hcont
          b0 residual C F) := by
  rw [case2DisplayedSourceTerminalProductPrefixCandidate]
  exact matrixEntryIdeal_submatrix_equiv
    (case2DisplayedSourceTerminalProductReindexedCandidate Wold n hS hcont
      b0 residual C F)
    (case2SourceTerminalRowEquivPrefixOfNotNext n hcont hstop).symm
    (Equiv.refl υ)

/-- Reindexing the source-row terminal product candidate preserves the
matrix-entry ideal of the stacked stopped terminal candidate. -/
theorem matrixEntryIdeal_sourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {J : ℕ}
    (Wold :
      Matrix (case2SourceOldTopRowIndex J) (case2SourceOldTopRowIndex J) R)
    (n : ℕ → ℕ) {S : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (F : Matrix τ υ R) :
    matrixEntryIdeal
        (case2DisplayedSourceTerminalProductReindexedCandidate Wold n hS hcont b0 residual C F) =
      matrixEntryIdeal
        (case2DisplayedPaperTerminalCprimeCandidate Wold
          (case2DisplayedSourceOldTopBlock (J := J) C)
          n hS hcont b0 residual C F) := by
  rw [case2DisplayedSourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate_submatrix]
  exact matrixEntryIdeal_submatrix_equiv
    (case2DisplayedPaperTerminalCprimeCandidate Wold
      (case2DisplayedSourceOldTopBlock (J := J) C)
      n hS hcont b0 residual C F)
    (case2SourceTerminalRowEquiv J).symm (Equiv.refl υ)

/-- Source-chart displayed Case 2 terminal product after the supplied `Q/P`
identity and failed next continuation.

The old top block `Ctop`, old top multiplier `Atop`, and remaining following
product `F` are still supplied.  The residual row weights are the successor
recurrence weights carried by the supplied displayed boundary.  This theorem
combines the source-chart `Q/P` identity with the weighted stopped-terminal
zero-row absorption; it does not identify the right hand side with Aoyagi's
full `C'^(S+1)` or prove chart production. -/
theorem exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (Atop : Matrix ι ι R) (Ctop : Matrix ι τ R)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (F : Matrix τ υ R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks Atop 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock Ctop
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * F) =
      matrixEntryIdeal
          (case2DisplayedPaperTerminalCprimeCandidate Atop Ctop n data.stage_pos
            data.continuation (post.weight (J + 1)) residual C F) := by
  rcases data.sourceDisplayedQP_sourceChartMap_paperQP residual C with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  let row := case2DisplayedPivotRow n data.stage_pos data.continuation
  let col := case2DisplayedPivotCol n data.stage_pos data.continuation
  let A := case2DisplayedPaperDchart n data.stage_pos data.continuation residual
  let Ltail : Matrix (Unit ⊕ pivotComplement row) (Unit ⊕ pivotComplement col) R :=
    weightedPivotBlockRowOp q (fun i ↦ pivotFirstX row col A i ()) *
      (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
        case2DisplayedSourceSubstitutionBlock n data.stage_pos data.continuation u
          residual).submatrix (pivotFirstIndexEquiv row) (pivotFirstIndexEquiv col)
  let Wtail : Matrix (Unit ⊕ pivotComplement row) (Unit ⊕ pivotComplement row) R :=
    weightedPivotDiagonal (post.weight (J + 1))
      (fun i : pivotComplement row ↦ post.weight (case2ResidualRowLevel n S J i.1))
  let Dppp : Matrix (Unit ⊕ pivotComplement row) (Unit ⊕ pivotComplement col) R :=
    case2DisplayedPaperDppp n data.stage_pos data.continuation residual
  let Csrc : Matrix (Unit ⊕ pivotComplement col) τ R :=
    case2DisplayedSourceFollowingFactor n data.stage_pos data.continuation C
  let Cprime : Matrix (Unit ⊕ pivotComplement col) τ R :=
    case2DisplayedPaperCprime n data.stage_pos data.continuation residual C
  have hq' : Ltail * Csrc = (Wtail * Dppp) * Cprime := by
    simpa [row, col, A, Ltail, Wtail, Dppp, Csrc, Cprime] using hq
  have hlift :
      fromBlocks Atop 0 0 Ltail * verticalBlock Ctop Csrc =
        fromBlocks Atop 0 0 (Wtail * Dppp) * verticalBlock Ctop Cprime := by
    exact fromBlocks_mul_verticalBlock_eq_of_tail Atop Ltail (Wtail * Dppp)
      Ctop Csrc Cprime hq'
  have hassoc :
      fromBlocks Atop 0 0 (Wtail * Dppp) * verticalBlock Ctop Cprime =
        fromBlocks Atop 0 0 Wtail * verticalBlock Ctop (Dppp * Cprime) := by
    rw [fromBlocks_mul_verticalBlock, fromBlocks_mul_verticalBlock, Matrix.mul_assoc]
  change
    matrixEntryIdeal ((fromBlocks Atop 0 0 Ltail * verticalBlock Ctop Csrc) * F) =
      matrixEntryIdeal
        (case2DisplayedPaperTerminalCprimeCandidate Atop Ctop n data.stage_pos
          data.continuation (post.weight (J + 1)) residual C F)
  calc
    matrixEntryIdeal ((fromBlocks Atop 0 0 Ltail * verticalBlock Ctop Csrc) * F)
        = matrixEntryIdeal
            ((fromBlocks Atop 0 0 (Wtail * Dppp) * verticalBlock Ctop Cprime) * F) := by
          rw [hlift]
    _ = matrixEntryIdeal
            ((fromBlocks Atop 0 0 Wtail * verticalBlock Ctop (Dppp * Cprime)) * F) := by
          rw [hassoc]
    _ = matrixEntryIdeal
          (verticalBlock ((Atop * Ctop) * F)
            (((show Matrix Unit Unit R from fun _ _ ↦ post.weight (J + 1)) *
              case2DisplayedPaperCprimeTop n data.stage_pos data.continuation residual C) *
              F)) := by
          simpa [row, Wtail, Dppp, Cprime] using
            matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack_of_not_next_cont
              (Wold := Atop) (Cold := Ctop) n data.stage_pos data.continuation
              hstop (post.weight (J + 1))
              (fun i : pivotComplement (case2DisplayedPivotRow n data.stage_pos
                    data.continuation) ↦
                post.weight (case2ResidualRowLevel n S J i.1))
              residual C F
    _ = matrixEntryIdeal
          (case2DisplayedPaperTerminalCprimeCandidate Atop Ctop n data.stage_pos
            data.continuation (post.weight (J + 1)) residual C F) := by
          rw [case2DisplayedPaperTerminalCprimeCandidate_eq_verticalBlock_mul]

/-- Source old-top/suffix specialization of the stopped displayed Case 2
terminal product.

The old top multiplier is now the source-shaped diagonal
`diag(pre.weight 1,...,pre.weight J)`, and the old top block is the source row
restriction of the supplied following matrix to rows `1,...,J`.  The suffix
`F` remains supplied, representing Aoyagi's remaining right product.  This is
still not a proof that the resulting stack is source-produced `C'^(S+1)`. -/
theorem exists_sourceDisplayedOldTopSuffixTerminalProduct_entryIdeal_eq_of_not_next_cont
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (F : Matrix τ υ R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * F) =
      matrixEntryIdeal
          (case2DisplayedPaperTerminalCprimeCandidate
            (case2DisplayedSourceOldTopWeight pre)
            (case2DisplayedSourceOldTopBlock C)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C F) :=
  data.exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont
    (case2DisplayedSourceOldTopWeight pre)
    (case2DisplayedSourceOldTopBlock C) hstop residual C F

/-- Source-row terminal-product version of the stopped displayed Case 2
source old-top/supplied-suffix theorem.

The right hand side is the one-based source-row presentation of the same
terminal candidate, with the following product kept as an arbitrary supplied
matrix `F`.  This is still only a reindexing of supplied terminal data; it does
not prove that the chart produces Aoyagi's full `C'^(S+1)`. -/
theorem exists_sourceOldTopSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (F : Matrix τ υ R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * F) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductReindexedCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C F) := by
  rcases data.exists_sourceDisplayedOldTopSuffixTerminalProduct_entryIdeal_eq_of_not_next_cont
      hstop residual C F with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    matrixEntryIdeal
        ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
            (weightedPivotBlockRowOp q
                  (fun i ↦
                    pivotFirstX
                      (case2DisplayedPivotRow n data.stage_pos data.continuation)
                      (case2DisplayedPivotCol n data.stage_pos data.continuation)
                      (case2DisplayedPaperDchart n data.stage_pos data.continuation
                        residual) i ()) *
                (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                  case2DisplayedSourceSubstitutionBlock n data.stage_pos
                    data.continuation u residual).submatrix
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotRow n data.stage_pos data.continuation))
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
            verticalBlock (case2DisplayedSourceOldTopBlock C)
              (case2DisplayedSourceFollowingFactor n data.stage_pos
                data.continuation C)) * F)
        =
      matrixEntryIdeal
          (case2DisplayedPaperTerminalCprimeCandidate
            (case2DisplayedSourceOldTopWeight pre)
            (case2DisplayedSourceOldTopBlock C)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C F) := hq
    _ =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductReindexedCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C F) := by
        rw [
          ← matrixEntryIdeal_sourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate]

/-- Source-row terminal-product theorem rewritten through a supplied terminal
`C'` bridge, with the following product kept as an arbitrary supplied matrix.

This consumes the explicit old-row and pivot-row equations carried by
`SuppliedTerminalCprimeBridge`; it does not prove that the bridge is produced
by the chart coordinates. -/
theorem exists_sourceOldTopSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (F : Matrix τ υ R)
    (bridge :
      SuppliedTerminalCprimeBridge n data.stage_pos data.continuation residual C) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * F) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre) (post.weight (J + 1)) *
            bridge.Cterm) * F) := by
  rcases data.exists_sourceOldTopSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont
      hstop residual C F with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    matrixEntryIdeal
        ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
            (weightedPivotBlockRowOp q
                  (fun i ↦
                    pivotFirstX
                      (case2DisplayedPivotRow n data.stage_pos data.continuation)
                      (case2DisplayedPivotCol n data.stage_pos data.continuation)
                      (case2DisplayedPaperDchart n data.stage_pos data.continuation
                        residual) i ()) *
                (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                  case2DisplayedSourceSubstitutionBlock n data.stage_pos
                    data.continuation u residual).submatrix
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotRow n data.stage_pos data.continuation))
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
            verticalBlock (case2DisplayedSourceOldTopBlock C)
              (case2DisplayedSourceFollowingFactor n data.stage_pos
                data.continuation C)) * F)
        =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductReindexedCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C F) := hq
    _ =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre) (post.weight (J + 1)) *
            bridge.Cterm) * F) := by
        rw [bridge.terminalProduct_eq_weight_mul_Cterm_mul
          (case2DisplayedSourceOldTopWeight pre) (post.weight (J + 1)) F]

/-- Source old-top specialization with the remaining right suffix named as
Aoyagi's raw paper-order matrix chain.

This only instantiates the already supplied suffix `F` with
`sourceSuffixProduct`; it does not construct Aoyagi's full source-produced
`C'^(S+1)`. -/
theorem exists_sourceDisplayedOldTopSourceSuffixProduct_entryIdeal_eq_of_not_next_cont
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          (case2DisplayedPaperTerminalCprimeCandidate
            (case2DisplayedSourceOldTopWeight pre)
            (case2DisplayedSourceOldTopBlock C)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C
            (sourceSuffixProduct κ Ctail S hSuffix)) :=
  data.exists_sourceDisplayedOldTopSuffixTerminalProduct_entryIdeal_eq_of_not_next_cont
    hstop residual C (sourceSuffixProduct κ Ctail S hSuffix)

/-- Source-row terminal-product version of the stopped displayed Case 2
source old-top/suffix theorem.

The right hand side is the one-based source-row presentation of the same
terminal candidate.  This is still only a reindexing of supplied terminal data;
it does not prove that the chart produces Aoyagi's full `C'^(S+1)`. -/
theorem exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductReindexedCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C
            (sourceSuffixProduct κ Ctail S hSuffix)) := by
  rcases data.exists_sourceDisplayedOldTopSourceSuffixProduct_entryIdeal_eq_of_not_next_cont
      κ hSuffix hstop residual C Ctail with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    matrixEntryIdeal
        ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
            (weightedPivotBlockRowOp q
                  (fun i ↦
                    pivotFirstX
                      (case2DisplayedPivotRow n data.stage_pos data.continuation)
                      (case2DisplayedPivotCol n data.stage_pos data.continuation)
                      (case2DisplayedPaperDchart n data.stage_pos data.continuation
                        residual) i ()) *
                (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                  case2DisplayedSourceSubstitutionBlock n data.stage_pos
                    data.continuation u residual).submatrix
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotRow n data.stage_pos data.continuation))
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
            verticalBlock (case2DisplayedSourceOldTopBlock C)
              (case2DisplayedSourceFollowingFactor n data.stage_pos
                data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix)
        =
      matrixEntryIdeal
          (case2DisplayedPaperTerminalCprimeCandidate
            (case2DisplayedSourceOldTopWeight pre)
            (case2DisplayedSourceOldTopBlock C)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C
            (sourceSuffixProduct κ Ctail S hSuffix)) := hq
    _ =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductReindexedCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C
            (sourceSuffixProduct κ Ctail S hSuffix)) := by
        rw [
          ← matrixEntryIdeal_sourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate]

/-- Source-row terminal-product theorem rewritten through a supplied terminal
`C'` bridge.

This consumes the explicit old-row and pivot-row equations carried by
`SuppliedTerminalCprimeBridge`; it does not prove that the bridge is produced
by the chart coordinates. -/
theorem exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R)
    (bridge :
      SuppliedTerminalCprimeBridge n data.stage_pos data.continuation residual C) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre) (post.weight (J + 1)) *
            bridge.Cterm) * sourceSuffixProduct κ Ctail S hSuffix) := by
  rcases data.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont
      κ hSuffix hstop residual C Ctail with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    matrixEntryIdeal
        ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
            (weightedPivotBlockRowOp q
                  (fun i ↦
                    pivotFirstX
                      (case2DisplayedPivotRow n data.stage_pos data.continuation)
                      (case2DisplayedPivotCol n data.stage_pos data.continuation)
                      (case2DisplayedPaperDchart n data.stage_pos data.continuation
                        residual) i ()) *
                (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                  case2DisplayedSourceSubstitutionBlock n data.stage_pos
                    data.continuation u residual).submatrix
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotRow n data.stage_pos data.continuation))
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
            verticalBlock (case2DisplayedSourceOldTopBlock C)
              (case2DisplayedSourceFollowingFactor n data.stage_pos
                data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix)
        =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductReindexedCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C
            (sourceSuffixProduct κ Ctail S hSuffix)) := hq
    _ =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre) (post.weight (J + 1)) *
            bridge.Cterm) * sourceSuffixProduct κ Ctail S hSuffix) := by
        rw [bridge.terminalProduct_eq_weight_mul_Cterm_mul
          (case2DisplayedSourceOldTopWeight pre) (post.weight (J + 1))
          (sourceSuffixProduct κ Ctail S hSuffix)]

/-- Terminal-prefix-row version of the stopped displayed Case 2 source
old-top/source suffix theorem.

The right hand side is indexed by the terminal prefix rows `1..M(S+1)`.  Under
the stopped hypotheses this row type is equivalent to `1..J+1`, since
`M(S+1)=J+1`.  This is still only a reindexing of supplied terminal data, not
chart production of Aoyagi's full next matrix. -/
theorem exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalPrefixProduct_of_not_next_cont
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductPrefixCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation hstop (post.weight (J + 1))
            residual C (sourceSuffixProduct κ Ctail S hSuffix)) := by
  rcases data.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont
      κ hSuffix hstop residual C Ctail with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    matrixEntryIdeal
        ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
            (weightedPivotBlockRowOp q
                  (fun i ↦
                    pivotFirstX
                      (case2DisplayedPivotRow n data.stage_pos data.continuation)
                      (case2DisplayedPivotCol n data.stage_pos data.continuation)
                      (case2DisplayedPaperDchart n data.stage_pos data.continuation
                        residual) i ()) *
                (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                  case2DisplayedSourceSubstitutionBlock n data.stage_pos
                    data.continuation u residual).submatrix
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotRow n data.stage_pos data.continuation))
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
            verticalBlock (case2DisplayedSourceOldTopBlock C)
              (case2DisplayedSourceFollowingFactor n data.stage_pos
                data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix)
        =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductReindexedCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation (post.weight (J + 1)) residual C
            (sourceSuffixProduct κ Ctail S hSuffix)) := hq
    _ =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductPrefixCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation hstop (post.weight (J + 1))
            residual C (sourceSuffixProduct κ Ctail S hSuffix)) := by
        rw [
          matrixEntryIdeal_sourceTerminalProductPrefixCandidate_eq_sourceTerminalProduct]

/-- Terminal-prefix-row stopped source old-top/source suffix theorem rewritten
through a supplied terminal `C'` bridge.

This is still a bridge consumer: it does not construct the supplied terminal
matrix from chart coordinates. -/
theorem exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalPrefixProduct_of_not_next_cont
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1))
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R)
    (bridge :
      SuppliedTerminalCprimeBridge n data.stage_pos data.continuation residual C) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeightPrefixCandidate
              (case2DisplayedSourceOldTopWeight pre)
              n data.continuation hstop (post.weight (J + 1)) *
            bridge.Cterm.submatrix
              (case2SourceTerminalRowEquivPrefixOfNotNext n data.continuation hstop).symm
              id) * sourceSuffixProduct κ Ctail S hSuffix) := by
  have hprefix :=
    data.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalPrefixProduct_of_not_next_cont
      κ hSuffix hstop residual C Ctail
  rcases hprefix with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    matrixEntryIdeal
        ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
            (weightedPivotBlockRowOp q
                  (fun i ↦
                    pivotFirstX
                      (case2DisplayedPivotRow n data.stage_pos data.continuation)
                      (case2DisplayedPivotCol n data.stage_pos data.continuation)
                      (case2DisplayedPaperDchart n data.stage_pos data.continuation
                        residual) i ()) *
                (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                  case2DisplayedSourceSubstitutionBlock n data.stage_pos
                    data.continuation u residual).submatrix
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotRow n data.stage_pos data.continuation))
                  (pivotFirstIndexEquiv
                    (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
            verticalBlock (case2DisplayedSourceOldTopBlock C)
              (case2DisplayedSourceFollowingFactor n data.stage_pos
                data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix)
        =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductPrefixCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation hstop (post.weight (J + 1))
            residual C (sourceSuffixProduct κ Ctail S hSuffix)) := hq
    _ =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeightPrefixCandidate
              (case2DisplayedSourceOldTopWeight pre)
              n data.continuation hstop (post.weight (J + 1)) *
            bridge.Cterm.submatrix
              (case2SourceTerminalRowEquivPrefixOfNotNext n data.continuation hstop).symm
              id) * sourceSuffixProduct κ Ctail S hSuffix) := by
        rw [bridge.terminalPrefixProduct_eq_weight_mul_CtermPrefix_mul
          (case2DisplayedSourceOldTopWeight pre) hstop (post.weight (J + 1))
          (sourceSuffixProduct κ Ctail S hSuffix)]

/-- Terminal-prefix-row stopped source old-top/source suffix theorem in the
current-prefix row-exhausted branch.

The row-exhaustion hypothesis supplies the stopped-continuation proof used to
index terminal prefix rows.  It does not assert actual next-width exhaustion
and does not simplify the transported pivot row to the original source row. -/
theorem exists_sourceOldTopSuffix_entryIdeal_eq_prefixProduct_of_rowExhausted
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hrow : prefixMinNat n S = J + 1)
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalProductPrefixCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n data.stage_pos data.continuation
            (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)
            (post.weight (J + 1)) residual C
            (sourceSuffixProduct κ Ctail S hSuffix)) :=
  data.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalPrefixProduct_of_not_next_cont
    κ hSuffix
    (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)
    residual C Ctail

/-- Current-prefix row-exhausted source old-top/source suffix theorem,
rewritten through the explicit transported-row terminal matrix.

The last row of the terminal matrix is the top row of `Q⁻¹ C`; in a
wide-next row-exhausted branch this row may include genuine post-pivot column
correction terms. -/
theorem exists_sourceOldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hrow : prefixMinNat n S = J + 1)
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeightPrefixCandidate
              (case2DisplayedSourceOldTopWeight pre)
              n data.continuation
              (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)
              (post.weight (J + 1)) *
            (case2DisplayedSourceTerminalTransportedRows n data.stage_pos
              data.continuation residual C).submatrix
              (case2SourceTerminalRowEquivPrefixOfNotNext n data.continuation
                (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)).symm
              id) * sourceSuffixProduct κ Ctail S hSuffix) :=
  data.exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalPrefixProduct_of_not_next_cont
    κ hSuffix
    (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)
    residual C Ctail
    (SuppliedTerminalCprimeBridge.of_transportedRows
      (n := n) (S := S) (J := J)
      (hS := data.stage_pos) (hcont := data.continuation)
      (residual := residual) (C := C))

/-- The displayed source-coordinate chart map has the selected variable as a
transformed finite-center value. -/
theorem displayedPivot_sourceChartMap_value_mem
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) :
    u ∈
      {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        case2DisplayedSourceChartMap n data.stage_pos data.continuation u
          residual p = v} :=
  case2DisplayedSourceChartMap_value_mem n data.stage_pos data.continuation u residual

/-- The displayed source-coordinate chart map makes every transformed finite
center generator divisible by the selected variable. -/
theorem displayedPivot_sourceChartMap_center_dvd
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) :
    ∀ p, p ∈ case2ResidualBlockPivotEntries n S J →
      u ∣ case2DisplayedSourceChartMap n data.stage_pos data.continuation u
        residual p :=
  case2DisplayedSourceChartMap_center_dvd n data.stage_pos data.continuation u residual

/-- The displayed source-coordinate chart map principalizes the finite
residual-block center ideal to the selected variable. -/
theorem displayedPivot_sourceChartMap_centerIdeal_eq_span_singleton
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) :
    Ideal.span
        {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
          case2DisplayedSourceChartMap n data.stage_pos data.continuation u
            residual p = v} =
      Ideal.span ({u} : Set R) :=
  case2DisplayedSourceChartMap_centerIdeal_eq_span_singleton
    n data.stage_pos data.continuation u residual

end Case2DisplayedSuppliedChartFamilyBoundary

/-- Supplied source-order data for the actual-width-exhausted displayed Case 2
terminal branch.

This packages the old top multiplier/block and remaining suffix used to read
the stopped displayed terminal product in source order.  The actual-width
exhaustion hypothesis is part of the model; without it, old `(S,J+1)` labels
need not relabel to `(S+1,0)`.  The fields remain supplied data, not
chart-produced source coordinates. -/
structure Case2DisplayedSuppliedActualWidthTerminalSourceModel
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    (L : ℕ) (n : ℕ → ℕ) {S J : ℕ}
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (b0 : R) (residual : ℕ × ℕ → R) (C : ℕ → τ → R) where
  Atop : Matrix ι ι R
  Ctop : Matrix ι τ R
  F : Matrix τ υ R
  actualWidth_exhausted : n (S + 1) = J + 1

namespace Case2DisplayedSuppliedActualWidthTerminalSourceModel

variable {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
variable {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
variable {hS : 1 ≤ S} {hSL : S ≤ L}
variable {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
variable {b0 : R} {residual : ℕ × ℕ → R} {C : ℕ → τ → R}

/-- The supplied source-order terminal weight candidate `blockdiag(Atop,[b0])`. -/
def terminalWeightCandidate
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := hS) (hSL := hSL) (hcont := hcont)
        (b0 := b0) (residual := residual) (C := C)) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalWeight
    model.Atop b0

/-- The supplied source-order terminal next-factor candidate `[Ctop;C0]`. -/
def terminalCnextCandidate
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := hS) (hSL := hSL) (hcont := hcont)
        (b0 := b0) (residual := residual) (C := C)) :
    Matrix (ι ⊕ Unit) τ R :=
  Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperTerminalCnext
    model.Ctop n hS hcont residual C

/-- The supplied source-order terminal product
`(blockdiag(Atop,[b0]) * [Ctop;C0]) * F`. -/
def terminalProductCandidate
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := hS) (hSL := hSL) (hcont := hcont)
        (b0 := b0) (residual := residual) (C := C)) :
    Matrix (ι ⊕ Unit) υ R :=
  (model.terminalWeightCandidate * model.terminalCnextCandidate) * model.F

/-- Actual-width exhaustion forces the displayed Case 2 next-continuation
bound to fail. -/
theorem not_next_cont_of_actualWidth_exhausted
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := hS) (hSL := hSL) (hcont := hcont)
        (b0 := b0) (residual := residual) (C := C)) :
    ¬ J + 2 ≤ prefixMinNat n (S + 1) := by
  intro hnext
  have hwidth : prefixMinNat n (S + 1) ≤ J + 1 := by
    simpa [model.actualWidth_exhausted] using
      (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))
  omega

/-- In the actual-width-exhausted terminal source model, the displayed pivot's
column complement is empty.  This is only the column-exhausted side; the row
complement may still be nonempty. -/
theorem displayedPivotColComplement_isEmpty
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := hS) (hSL := hSL) (hcont := hcont)
        (b0 := b0) (residual := residual) (C := C)) :
    IsEmpty (pivotComplement (case2DisplayedPivotCol n hS hcont)) :=
  case2DisplayedPivotColComplement_isEmpty_of_width_next_eq hS hcont
    model.actualWidth_exhausted

/-- Under actual-width exhaustion, old `(S,J+1)` introduced labels match the
stage-relabelled `(S+1,0)` introduced labels. -/
theorem introducedLabel_terminal_iff_succStage_zero
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := hS) (hSL := hSL) (hcont := hcont)
        (b0 := b0) (residual := residual) (C := C))
    (s k : ℕ) :
    introducedLabel L n S (J + 1) s k ↔
      introducedLabel L n (S + 1) 0 s k :=
  introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq
    L n model.actualWidth_exhausted

/-- Finite-set form of
`Case2DisplayedSuppliedActualWidthTerminalSourceModel.
introducedLabel_terminal_iff_succStage_zero`. -/
theorem introducedLabelFinset_terminal_eq_succStage_zero
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := hS) (hSL := hSL) (hcont := hcont)
        (b0 := b0) (residual := residual) (C := C)) :
    introducedLabelFinset L n S (J + 1) =
      introducedLabelFinset L n (S + 1) 0 :=
  introducedLabelFinset_currentSucc_eq_succStage_zero_of_nextWidth_eq
    L n model.actualWidth_exhausted

end Case2DisplayedSuppliedActualWidthTerminalSourceModel

namespace Case2DisplayedSuppliedChartFamilyBoundary

/-- Actual-width-exhausted source-model wrapper for the displayed Case 2
terminal product.

The model supplies the old top multiplier/block, suffix, and the actual-width
exhaustion that lets the terminal stopped branch be read at `(S+1,0)`.  The
theorem is still a supplied-boundary entry-ideal statement: it does not prove
that the supplied fields are chart-produced source data, nor does it prove
chart coverage, Jacobian arithmetic, normal crossings, RLCT extraction,
termination, or a transition invariant. -/
theorem exists_weightedTerminalProduct_entryIdeal_eq_terminalProductCandidate_of_actualWidth
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := data.stage_pos) (hSL := data.stage_le) (hcont := data.continuation)
        (b0 := post.weight (J + 1)) (residual := residual) (C := C)) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks model.Atop 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock model.Ctop
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * model.F) =
      matrixEntryIdeal model.terminalProductCandidate := by
  simpa [Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalProductCandidate,
    Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalWeightCandidate,
    Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalCnextCandidate,
    case2DisplayedPaperTerminalCprimeCandidate] using
    (data.exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont
      model.Atop model.Ctop model.not_next_cont_of_actualWidth_exhausted residual C model.F)

/-- Candidate `(S+1,0)` recurrence state obtained by relabelling the supplied
displayed Case 2 post-state.

This copies the supplied post-state's level and variable maps.  Actual-width
exhaustion is used only in the accompanying projection lemmas to show that the
introduced-label products and certificate domains agree. -/
def terminalRelabelPost
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (_data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    IntroducedLabelRecurrenceState L n (S + 1) 0 R :=
  post.stageRelabelSuccZero

theorem terminalRelabelPost_level
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    (data.terminalRelabelPost).level s k = post.level s k :=
  rfl

theorem terminalRelabelPost_var
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J s k : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular) :
    (data.terminalRelabelPost).var s k = post.var s k :=
  rfl

/-- Under actual-width exhaustion, the relabelled post-state has the same
finite-product recurrence factors as the old displayed post-state. -/
theorem terminalRelabelPost_step_eq_of_actualWidth
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hwidth : n (S + 1) = J + 1) :
    data.terminalRelabelPost.step = post.step :=
  post.stageRelabelSuccZero_step_eq hwidth

/-- Under actual-width exhaustion, the relabelled post-state has the same row
weights as the old displayed post-state. -/
theorem terminalRelabelPost_weight_eq_of_actualWidth
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J i : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hwidth : n (S + 1) = J + 1) :
    data.terminalRelabelPost.weight i = post.weight i :=
  post.stageRelabelSuccZero_weight_eq hwidth

/-- Source-chart displayed Case 2 terminal product with the surviving pivot
weight read from the relabelled `(S+1,0)` post-state.

This is a supplied-boundary terminal-product statement.  Actual-width
exhaustion supplies both failed next continuation and the equality between the
old post-state weight and the relabelled post-state weight. -/
theorem exists_sourceTerminalEntryIdeal_eq_relabelCandidate_of_actualWidth
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (Atop : Matrix ι ι R) (Ctop : Matrix ι τ R)
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (F : Matrix τ υ R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks Atop 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock Ctop
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * F) =
      matrixEntryIdeal
          (case2DisplayedPaperTerminalCprimeCandidate Atop Ctop n data.stage_pos
            data.continuation (data.terminalRelabelPost.weight (J + 1))
            residual C F) := by
  have hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1) := by
    intro hnext
    have hwidth_le : prefixMinNat n (S + 1) ≤ J + 1 := by
      simpa [hwidth] using
        (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))
    omega
  have hweight :
      data.terminalRelabelPost.weight (J + 1) = post.weight (J + 1) :=
    data.terminalRelabelPost_weight_eq_of_actualWidth hwidth
  rw [hweight]
  exact
    data.exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont
      Atop Ctop hstop residual C F

/-- Source old-top/supplied-suffix theorem with a supplied terminal `C'`, with
the surviving pivot weight read from the relabelled `(S+1,0)` post-state.

This uses actual-width exhaustion only to identify the relabelled pivot weight
with the displayed post-state pivot weight and to force the stopped branch. -/
theorem exists_oldTopSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (F : Matrix τ υ R)
    (bridge :
      SuppliedTerminalCprimeBridge n data.stage_pos data.continuation residual C) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * F) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              (data.terminalRelabelPost.weight (J + 1)) *
            bridge.Cterm) * F) := by
  have hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1) := by
    intro hnext
    have hwidth_le : prefixMinNat n (S + 1) ≤ J + 1 := by
      simpa [hwidth] using
        (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))
    omega
  have hweight :
      data.terminalRelabelPost.weight (J + 1) = post.weight (J + 1) :=
    data.terminalRelabelPost_weight_eq_of_actualWidth hwidth
  rw [hweight]
  exact
    exists_sourceOldTopSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont
      data hstop residual C F bridge

/-- Source old-top/supplied-suffix theorem in the actual-width terminal branch,
with terminal `C'` specialized to the original source rows `1,...,J+1`.

This consumes only the column-exhaustion bridge
`SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq`.  It still does
not construct the old top multiplier, suffix product, chart coverage, Jacobian
arithmetic, normal crossings, or RLCT extraction. -/
theorem exists_oldTopSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R) (F : Matrix τ υ R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * F) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              (data.terminalRelabelPost.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C) * F) :=
  data.exists_oldTopSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth
    hwidth residual C F
    (SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq
      n data.stage_pos data.continuation hwidth residual C)

/-- Source old-top/source suffix theorem with a supplied terminal `C'`, with
the surviving pivot weight read from the relabelled `(S+1,0)` post-state.

This uses actual-width exhaustion only to identify the relabelled pivot weight
with the displayed post-state pivot weight and to force the stopped branch. -/
theorem exists_oldTopSourceSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R)
    (bridge :
      SuppliedTerminalCprimeBridge n data.stage_pos data.continuation residual C) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              (data.terminalRelabelPost.weight (J + 1)) *
            bridge.Cterm) * sourceSuffixProduct κ Ctail S hSuffix) := by
  have hstop : ¬ J + 2 ≤ prefixMinNat n (S + 1) := by
    intro hnext
    have hwidth_le : prefixMinNat n (S + 1) ≤ J + 1 := by
      simpa [hwidth] using
        (prefixMinNat_le_width n (by omega : 1 ≤ S + 1))
    omega
  have hweight :
      data.terminalRelabelPost.weight (J + 1) = post.weight (J + 1) :=
    data.terminalRelabelPost_weight_eq_of_actualWidth hwidth
  rw [hweight]
  exact
    exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont
      data κ hSuffix hstop residual C Ctail bridge

/-- Source old-top/source suffix theorem in the actual-width terminal branch,
with terminal `C'` specialized to the original source rows `1,...,J+1`.

This consumes only the column-exhaustion bridge
`SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq`.  It still does
not construct the old top multiplier, suffix product, chart coverage,
Jacobian arithmetic, normal crossings, or RLCT extraction. -/
theorem exists_oldTopSourceSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (hwidth : n (S + 1) = J + 1)
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              (data.terminalRelabelPost.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C) *
              sourceSuffixProduct κ Ctail S hSuffix) :=
  data.exists_oldTopSourceSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth
    κ hSuffix hwidth residual C Ctail
    (SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq
      n data.stage_pos data.continuation hwidth residual C)

/-- Actual-width source-model wrapper for the terminal product whose surviving
pivot weight is read from the relabelled `(S+1,0)` post-state.

The model still supplies the old top multiplier/block and suffix.  This only
replaces the old post-state pivot weight by the equal relabelled post-state
weight; it does not construct Aoyagi's next following matrix. -/
theorem exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_actualWidth
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := data.stage_pos) (hSL := data.stage_le) (hcont := data.continuation)
        (b0 := data.terminalRelabelPost.weight (J + 1)) (residual := residual)
        (C := C)) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          ((fromBlocks model.Atop 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock model.Ctop
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) * model.F) =
      matrixEntryIdeal model.terminalProductCandidate := by
  simpa [Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalProductCandidate,
    Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalWeightCandidate,
    Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalCnextCandidate,
    case2DisplayedPaperTerminalCprimeCandidate] using
    (data.exists_sourceTerminalEntryIdeal_eq_relabelCandidate_of_actualWidth
      model.Atop model.Ctop model.actualWidth_exhausted residual C model.F)

/-- Actual-width terminal source-model theorem for the concrete displayed
source-chart Case 2 boundary.

This constructor uses the displayed source chart's pivot value for the concrete
successor recurrence state and the corrected selected-label exponent update.
The chart-family regularity predicates and the terminal old-top/suffix model
are still supplied. -/
theorem exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_sourceChartMap_actualWidth
    {ι υ τ R : Type*} [CommRing R] [Fintype ι] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R) (C : ℕ → τ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (model :
      Case2DisplayedSuppliedActualWidthTerminalSourceModel
        (ι := ι) (υ := υ) (τ := τ) (R := R)
        (L := L) (n := n) (S := S) (J := J)
        (hS := hS) (hSL := hSL) (hcont := hcont)
        (b0 :=
          (pre.case2Succ
            (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
            |>.stageRelabelSuccZero
            |>.weight (J + 1))
        (residual := residual) (C := C)) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          ((fromBlocks model.Atop 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock model.Ctop
                (case2DisplayedSourceFollowingFactor n hS hcont C)) * model.F) =
      matrixEntryIdeal model.terminalProductCandidate := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  simpa [data] using
    (data.exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_actualWidth
      residual C model)

/-- Actual-width source-chart Case 2 terminal theorem with an arbitrary supplied
following product and terminal `C'` specialized to original source rows.

This composes the concrete displayed source-chart boundary with the
actual-width original-row terminal bridge.  It removes arbitrary recurrence
post-data and arbitrary terminal `Cterm`, but `F` remains supplied. -/
theorem exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (C : ℕ → τ → R) (F : Matrix τ υ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) * F) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C) * F) := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  simpa [data] using
    (data.exists_oldTopSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth
      hwidth residual C F)

/-- Actual-width source-chart Case 2 terminal source-suffix theorem with the
terminal `C'` specialized to original source rows.

This composes the concrete displayed source-chart boundary with the
actual-width original-row terminal bridge.  It removes arbitrary recurrence
post-data and arbitrary terminal `Cterm`, but it still does not prove chart
coverage, Jacobian arithmetic, normal crossings, RLCT extraction, termination,
or transition invariance. -/
theorem exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) *
            sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C) *
              sourceSuffixProduct κ Ctail S hSuffix) := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  simpa [data] using
    (data.exists_oldTopSourceSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth
      κ hSuffix hwidth residual C Ctail)

/-- Row-exhausted source-chart Case 2 terminal source-suffix theorem with the
terminal `C'` written as transported rows.

This composes the concrete displayed source-chart boundary with the
row-exhausted transported-row terminal bridge.  The pivot row remains the top
row of `Q⁻¹ C`, so this theorem does not assert actual next-width exhaustion
or original-row equality for row `J+1`. -/
theorem exists_sourceChart_oldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hrow : prefixMinNat n S = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) *
            sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeightPrefixCandidate
              (case2DisplayedSourceOldTopWeight pre)
              n hcont (case2_not_next_cont_of_prefixMin_current_eq hS hrow)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.weight (J + 1)) *
            (case2DisplayedSourceTerminalTransportedRows n hS hcont residual C).submatrix
              (case2SourceTerminalRowEquivPrefixOfNotNext n hcont
                (case2_not_next_cont_of_prefixMin_current_eq hS hrow)).symm id) *
            sourceSuffixProduct κ Ctail S hSuffix) := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  simpa [data] using
    (data.exists_sourceOldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
      κ hSuffix hrow residual C Ctail)

/-- Actual-width relabel of the displayed Case 2 post-state's level invariant. -/
theorem terminalRelabelPostLevelInvariants_of_actualWidth
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hwidth : n (S + 1) = J + 1) :
    IntroducedLabelLevelInvariants L n (S + 1) 0
      data.terminalRelabelPost.level leastValue' := by
  simpa [terminalRelabelPost] using
    data.postLevelInvariants.relabel_currentSucc_succStage_zero_of_nextWidth_eq
      hwidth

/-- Actual-width relabel of the displayed Case 2 exponent certificate domain. -/
theorem terminalRelabelExponentDomain_of_actualWidth
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (hwidth : n (S + 1) = J + 1) :
    IntroducedLabelExponentCertificates L n (S + 1) 0 t' numerator' leastValue' :=
  data.extendExponentDomain.relabel_currentSucc_succStage_zero_of_nextWidth_eq
    hwidth

/-- Actual-width displayed source-chart terminal boundary.

This packages the terminal source-suffix entry-ideal statement with the
actual-width relabelled level and exponent-domain data.  It is a boundary
package for the displayed source chart: it does not prove chart coverage,
source production of `C'^(S+1)`, Jacobian arithmetic, normal crossings, RLCT
extraction, termination, or transition invariance. -/
theorem sourceChart_actualWidth_terminalOriginalRowsBoundary
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : S + 1 ≤ L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) *
            sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C) *
              sourceSuffixProduct κ Ctail S hSuffix)) ∧
    IntroducedLabelLevelInvariants L n (S + 1) 0
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
        |>.stageRelabelSuccZero
        |>.level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelExponentCertificates L n (S + 1) 0
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  refine ⟨?_, ?_, ?_⟩
  · exact
      exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
        pre u residual hS hSL hcont hwidth exponentPre levelInv leastValueGap
        chartFamily κ hSuffix C Ctail
  · simpa [data, terminalRelabelPost] using
      (data.terminalRelabelPostLevelInvariants_of_actualWidth hwidth)
  · simpa [data] using
      (data.terminalRelabelExponentDomain_of_actualWidth hwidth)

/-- Actual-width displayed source-chart terminal boundary with an arbitrary
supplied following matrix.

This packages the terminal entry-ideal statement with the actual-width
relabelled level and exponent-domain data.  The following matrix `F` is still
supplied: this theorem does not construct the remaining right product, chart
coverage, source production of `C'^(S+1)`, Jacobian arithmetic, normal
crossings, RLCT extraction, termination, or transition invariance. -/
theorem sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (C : ℕ → τ → R) (F : Matrix τ υ R) :
    (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) * F) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C) * F)) ∧
    IntroducedLabelLevelInvariants L n (S + 1) 0
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
        |>.stageRelabelSuccZero
        |>.level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelExponentCertificates L n (S + 1) 0
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  refine ⟨?_, ?_, ?_⟩
  · exact
      exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
        pre u residual hS hSL hcont hwidth exponentPre levelInv leastValueGap
        chartFamily C F
  · simpa [data, terminalRelabelPost] using
      (data.terminalRelabelPostLevelInvariants_of_actualWidth hwidth)
  · simpa [data] using
      (data.terminalRelabelExponentDomain_of_actualWidth hwidth)

/-- Multiplication by an identity matrix transported along an endpoint equality
does not change the matrix-entry ideal. -/
theorem matrixEntryIdeal_mul_ndrec_one
    {R : Type*} [CommRing R]
    {α : Type*} {κ : α → Type*} {i j : α}
    [Fintype (κ i)] [DecidableEq (κ i)]
    {m : Type*} (A : Matrix m (κ i) R) (h : i = j) :
    matrixEntryIdeal
        (A *
          Eq.ndrec
            (motive := fun j ↦ Matrix (κ i) (κ j) R)
            (1 : Matrix (κ i) (κ i) R) h) =
      matrixEntryIdeal A := by
  subst j
  simp

/-- In the terminal-last case, multiplying on the right by Aoyagi's raw source
suffix does not change the matrix-entry ideal. -/
theorem matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast
    {R : Type*} [CommRing R]
    {L : ℕ}
    (κ : Fin (L + 1) → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R)
    {S : ℕ} (hSuffix : S + 1 ≤ L) (hLast : S + 1 = L)
    {ι : Type*}
    (A : Matrix ι (κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix))) R) :
    matrixEntryIdeal (A * sourceSuffixProduct κ Ctail S hSuffix) =
      matrixEntryIdeal A := by
  rw [sourceSuffixProduct_terminalLast_eq_cast_one κ Ctail S hSuffix hLast]
  simpa using
    (matrixEntryIdeal_mul_ndrec_one
      (A := A)
      (h := sourceLayerIndex_terminalLast (L := L) (S := S) hLast))

/-- Actual-width displayed source-chart terminal boundary with identity as the
supplied following matrix.

This is the `F = 1` specialization of the arbitrary-following boundary.  It is
the algebraic shape needed after a separate terminal-last argument identifies
the source suffix as empty; it does not itself prove that a source suffix is
empty or chart-produced. -/
theorem sourceChart_actualWidth_terminalOriginalRowsIdentityFollowingBoundary
    {τ R : Type*} [CommRing R] [Finite τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (C : ℕ → τ → R) :
    (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          (fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C)) ∧
    IntroducedLabelLevelInvariants L n (S + 1) 0
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
        |>.stageRelabelSuccZero
        |>.level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelExponentCertificates L n (S + 1) 0
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) := by
  classical
  letI := Fintype.ofFinite τ
  rcases
      sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary
        pre u residual hS hSL hcont hwidth exponentPre levelInv leastValueGap
        chartFamily C (1 : Matrix τ τ R) with
    ⟨hentry, hlevel, hexponent⟩
  refine ⟨?_, hlevel, hexponent⟩
  rcases hentry with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  simpa using hq

/-- Actual-width source-chart Case 2 terminal-last theorem with the terminal
`C'` specialized to original source rows.

This consumes Aoyagi's raw source suffix and the terminal-last identity
`S+1=L`; it is not merely an arbitrary supplied-following specialization. -/
theorem exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_originalRowsProduct_of_actualWidth
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Finite (κ i)]
    (hSuffix : S + 1 ≤ L) (hLast : S + 1 = L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          (fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
      case2DisplayedSourceTerminalOriginalRows C) := by
  classical
  letI : ∀ i : Fin (L + 1), Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
  rcases
      exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
        pre u residual hS hSL hcont hwidth exponentPre levelInv leastValueGap
        chartFamily κ hSuffix C Ctail with
    ⟨q, hq⟩
  refine ⟨q, ?_⟩
  let Mq :=
    fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
        (weightedPivotBlockRowOp q
              (fun i ↦
                pivotFirstX
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont)
                  (case2DisplayedPaperDchart n hS hcont residual) i ()) *
            (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
              case2DisplayedSourceSubstitutionBlock n hS hcont
                (case2DisplayedSourceChartMap n hS hcont u residual
                  (J + 1, J + 1)) residual).submatrix
              (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
              (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
        verticalBlock (case2DisplayedSourceOldTopBlock C)
          (case2DisplayedSourceFollowingFactor n hS hcont C)
  let T :=
    case2DisplayedSourceTerminalWeight
        (case2DisplayedSourceOldTopWeight pre)
        ((pre.case2Succ
          (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
          |>.stageRelabelSuccZero
          |>.weight (J + 1)) *
      case2DisplayedSourceTerminalOriginalRows C
  change matrixEntryIdeal Mq = matrixEntryIdeal T
  calc
    matrixEntryIdeal Mq =
        matrixEntryIdeal (Mq * sourceSuffixProduct κ Ctail S hSuffix) := by
      exact (matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast
        κ Ctail hSuffix hLast Mq).symm
    _ = matrixEntryIdeal (T * sourceSuffixProduct κ Ctail S hSuffix) := by
      simpa [Mq, T] using hq
    _ = matrixEntryIdeal T := by
      exact matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast
        κ Ctail hSuffix hLast T

/-- Actual-width displayed source-chart terminal-last boundary.

This packages the terminal-last source-suffix entry-ideal statement with the
actual-width relabelled level and exponent-domain data.  It does not prove
chart coverage, source production of `C'^(S+1)`, chart-produced following
products, Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair. -/
theorem sourceChart_actualWidth_terminalLastOriginalRowsBoundary
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Finite (κ i)]
    (hSuffix : S + 1 ≤ L) (hLast : S + 1 = L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          (fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C)) ∧
    IntroducedLabelLevelInvariants L n (S + 1) 0
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
        |>.stageRelabelSuccZero
        |>.level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelExponentCertificates L n (S + 1) 0
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) := by
  classical
  letI : ∀ i : Fin (L + 1), Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  refine ⟨?_, ?_, ?_⟩
  · exact
      exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_originalRowsProduct_of_actualWidth
        pre u residual hS hSL hcont hwidth exponentPre levelInv leastValueGap
        chartFamily κ hSuffix hLast C Ctail
  · simpa [data, terminalRelabelPost] using
      (data.terminalRelabelPostLevelInvariants_of_actualWidth hwidth)
  · simpa [data] using
      (data.terminalRelabelExponentDomain_of_actualWidth hwidth)

/-- Row-exhausted terminal-last theorem with transported terminal prefix rows.

This consumes Aoyagi's raw source suffix under `S+1=L`, but keeps the
row-exhausted terminal matrix as transported prefix rows.  It does not assert
actual next-width exhaustion, original-row equality for row `J+1`, relabelled
`(S+1,0)` recurrence data, chart coverage, source production, Jacobian
arithmetic, normal crossings/RLCT, termination, transition invariance, or
printed-vector repair. -/
theorem exists_sourceOldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState L n S J R}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) R}
    {u : R}
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (data :
      Case2DisplayedSuppliedChartFamilyBoundary R L n S J
        t t' numerator numerator' leastValue leastValue'
        pre post u ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Finite (κ i)]
    (hSuffix : S + 1 ≤ L) (hLast : S + 1 = L)
    (hrow : prefixMinNat n S = J + 1)
    (residual : ℕ × ℕ → R)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement
        (case2DisplayedPivotRow n data.stage_pos data.continuation) → R,
      matrixEntryIdeal
          (fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n data.stage_pos data.continuation)
                        (case2DisplayedPivotCol n data.stage_pos data.continuation)
                        (case2DisplayedPaperDchart n data.stage_pos data.continuation
                          residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n data.stage_pos
                      data.continuation u residual).submatrix
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotRow n data.stage_pos data.continuation))
                    (pivotFirstIndexEquiv
                      (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n data.stage_pos
                  data.continuation C)) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalWeightPrefixCandidate
              (case2DisplayedSourceOldTopWeight pre)
              n data.continuation
              (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)
              (post.weight (J + 1)) *
            (case2DisplayedSourceTerminalTransportedRows n data.stage_pos
              data.continuation residual C).submatrix
              (case2SourceTerminalRowEquivPrefixOfNotNext n data.continuation
                (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)).symm
              id) := by
  classical
  letI : ∀ i : Fin (L + 1), Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
  rcases
      data.exists_sourceOldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
        κ hSuffix hrow residual C Ctail with
    ⟨q, hq⟩
  refine ⟨q, ?_⟩
  let Mq :=
    fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
        (weightedPivotBlockRowOp q
              (fun i ↦
                pivotFirstX
                  (case2DisplayedPivotRow n data.stage_pos data.continuation)
                  (case2DisplayedPivotCol n data.stage_pos data.continuation)
                  (case2DisplayedPaperDchart n data.stage_pos data.continuation
                    residual) i ()) *
            (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
              case2DisplayedSourceSubstitutionBlock n data.stage_pos
                data.continuation u residual).submatrix
              (pivotFirstIndexEquiv
                (case2DisplayedPivotRow n data.stage_pos data.continuation))
              (pivotFirstIndexEquiv
                (case2DisplayedPivotCol n data.stage_pos data.continuation))) *
        verticalBlock (case2DisplayedSourceOldTopBlock C)
          (case2DisplayedSourceFollowingFactor n data.stage_pos
            data.continuation C)
  let T :=
    case2DisplayedSourceTerminalWeightPrefixCandidate
        (case2DisplayedSourceOldTopWeight pre)
        n data.continuation
        (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)
        (post.weight (J + 1)) *
      (case2DisplayedSourceTerminalTransportedRows n data.stage_pos
        data.continuation residual C).submatrix
        (case2SourceTerminalRowEquivPrefixOfNotNext n data.continuation
          (case2_not_next_cont_of_prefixMin_current_eq data.stage_pos hrow)).symm
        id
  change matrixEntryIdeal Mq = matrixEntryIdeal T
  calc
    matrixEntryIdeal Mq =
        matrixEntryIdeal (Mq * sourceSuffixProduct κ Ctail S hSuffix) := by
      exact (matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast
        κ Ctail hSuffix hLast Mq).symm
    _ = matrixEntryIdeal (T * sourceSuffixProduct κ Ctail S hSuffix) := by
      simpa [Mq, T] using hq
    _ = matrixEntryIdeal T := by
      exact matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast
        κ Ctail hSuffix hLast T

/-- Source-chart row-exhausted terminal-last theorem with transported terminal
prefix rows.

This specializes the supplied row-exhausted terminal-last theorem to the
displayed source chart map.  The row `J+1` remains the top row of `Q⁻¹ C`; the
theorem does not identify it with the original source row or relabel the state
to `(S+1,0)`. -/
theorem exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hrow : prefixMinNat n S = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Finite (κ i)]
    (hSuffix : S + 1 ≤ L) (hLast : S + 1 = L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          (fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalWeightPrefixCandidate
              (case2DisplayedSourceOldTopWeight pre)
              n hcont (case2_not_next_cont_of_prefixMin_current_eq hS hrow)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.weight (J + 1)) *
            (case2DisplayedSourceTerminalTransportedRows n hS hcont residual C).submatrix
              (case2SourceTerminalRowEquivPrefixOfNotNext n hcont
                (case2_not_next_cont_of_prefixMin_current_eq hS hrow)).symm id) := by
  let data :=
    of_sourceChartMap_case2Succ_updateSelected pre u residual hS hSL hcont
      exponentPre levelInv leastValueGap chartFamily
  simpa [data] using
    (data.exists_sourceOldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
      κ hSuffix hLast hrow residual C Ctail)

/-- Actual-width displayed source-chart terminal boundary together with finite
center principalization.

This packages the actual-width original-row terminal entry-ideal statement and
the relabelled `(S+1,0)` certificates with the elementary fact that the
displayed source-coordinate chart principalizes the finite residual-block
center ideal to `Ideal.span {u}`.  The chart-family regularity interface and
the following matrix `F` remain supplied. -/
theorem sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (C : ℕ → τ → R) (F : Matrix τ υ R) :
    (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) * F) =
      matrixEntryIdeal
          ((case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C) * F)) ∧
    IntroducedLabelLevelInvariants L n (S + 1) 0
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
        |>.stageRelabelSuccZero
        |>.level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelExponentCertificates L n (S + 1) 0
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    u ∈
      {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        case2DisplayedSourceChartMap n hS hcont u residual p = v} ∧
    (∀ p, p ∈ case2ResidualBlockPivotEntries n S J →
      u ∣ case2DisplayedSourceChartMap n hS hcont u residual p) ∧
    Ideal.span
        {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
          case2DisplayedSourceChartMap n hS hcont u residual p = v} =
      Ideal.span ({u} : Set R) := by
  rcases
      sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary
        pre u residual hS hSL hcont hwidth exponentPre levelInv leastValueGap
        chartFamily C F with
    ⟨hentry, hlevel, hexponent⟩
  exact
    ⟨hentry, hlevel, hexponent,
      case2DisplayedSourceChartMap_value_mem n hS hcont u residual,
      case2DisplayedSourceChartMap_center_dvd n hS hcont u residual,
      case2DisplayedSourceChartMap_centerIdeal_eq_span_singleton n hS hcont u residual⟩

/-- Actual-width terminal-last source-chart boundary together with finite
center principalization.

This combines the terminal-last original-row boundary with the elementary fact
that the displayed source-coordinate chart principalizes the finite
residual-block center ideal to `Ideal.span {u}`.  It still does not prove chart
coverage, source production, Jacobian arithmetic, normal crossings/RLCT,
termination, transition invariance, or printed-vector repair. -/
theorem sourceChart_actualWidth_terminalLastOriginalRowsBoundary_withFiniteCenterIdeal
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hwidth : n (S + 1) = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Finite (κ i)]
    (hSuffix : S + 1 ≤ L) (hLast : S + 1 = L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          (fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalWeight
              (case2DisplayedSourceOldTopWeight pre)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.stageRelabelSuccZero
                |>.weight (J + 1)) *
            case2DisplayedSourceTerminalOriginalRows C)) ∧
    IntroducedLabelLevelInvariants L n (S + 1) 0
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
        |>.stageRelabelSuccZero
        |>.level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelExponentCertificates L n (S + 1) 0
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    u ∈
      {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        case2DisplayedSourceChartMap n hS hcont u residual p = v} ∧
    (∀ p, p ∈ case2ResidualBlockPivotEntries n S J →
      u ∣ case2DisplayedSourceChartMap n hS hcont u residual p) ∧
    Ideal.span
        {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
          case2DisplayedSourceChartMap n hS hcont u residual p = v} =
      Ideal.span ({u} : Set R) := by
  rcases
      sourceChart_actualWidth_terminalLastOriginalRowsBoundary
        pre u residual hS hSL hcont hwidth exponentPre levelInv leastValueGap
        chartFamily κ hSuffix hLast C Ctail with
    ⟨hentry, hlevel, hexponent⟩
  exact
    ⟨hentry, hlevel, hexponent,
      case2DisplayedSourceChartMap_value_mem n hS hcont u residual,
      case2DisplayedSourceChartMap_center_dvd n hS hcont u residual,
      case2DisplayedSourceChartMap_centerIdeal_eq_span_singleton n hS hcont u residual⟩

/-- Row-exhausted terminal-last source-chart boundary together with finite
center principalization.

The terminal side remains transported prefix rows; no original-row equality or
`(S+1,0)` relabelled certificate is asserted.  The finite-center part is only
principalization of the residual-block center ideal, not terminal-product
principalization, chart coverage, source production, Jacobian arithmetic,
normal crossings/RLCT, termination, transition invariance, or printed-vector
repair. -/
theorem sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hrow : prefixMinNat n S = J + 1)
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular)
    (κ : Fin (L + 1) → Type*) [∀ i, Finite (κ i)]
    (hSuffix : S + 1 ≤ L) (hLast : S + 1 = L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) :
    (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      matrixEntryIdeal
          (fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
              (weightedPivotBlockRowOp q
                    (fun i ↦
                      pivotFirstX
                        (case2DisplayedPivotRow n hS hcont)
                        (case2DisplayedPivotCol n hS hcont)
                        (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                  (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                    case2DisplayedSourceSubstitutionBlock n hS hcont
                      (case2DisplayedSourceChartMap n hS hcont u residual
                        (J + 1, J + 1)) residual).submatrix
                    (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                    (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
              verticalBlock (case2DisplayedSourceOldTopBlock C)
                (case2DisplayedSourceFollowingFactor n hS hcont C)) =
      matrixEntryIdeal
          (case2DisplayedSourceTerminalWeightPrefixCandidate
              (case2DisplayedSourceOldTopWeight pre)
              n hcont (case2_not_next_cont_of_prefixMin_current_eq hS hrow)
              ((pre.case2Succ
                (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
                |>.weight (J + 1)) *
            (case2DisplayedSourceTerminalTransportedRows n hS hcont residual C).submatrix
              (case2SourceTerminalRowEquivPrefixOfNotNext n hcont
                (case2_not_next_cont_of_prefixMin_current_eq hS hrow)).symm id)) ∧
    u ∈
      {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        case2DisplayedSourceChartMap n hS hcont u residual p = v} ∧
    (∀ p, p ∈ case2ResidualBlockPivotEntries n S J →
      u ∣ case2DisplayedSourceChartMap n hS hcont u residual p) ∧
    Ideal.span
        {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
          case2DisplayedSourceChartMap n hS hcont u residual p = v} =
      Ideal.span ({u} : Set R) := by
  exact
    ⟨exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
        pre u residual hS hSL hcont hrow exponentPre levelInv leastValueGap
        chartFamily κ hSuffix hLast C Ctail,
      case2DisplayedSourceChartMap_value_mem n hS hcont u residual,
      case2DisplayedSourceChartMap_center_dvd n hS hcont u residual,
      case2DisplayedSourceChartMap_centerIdeal_eq_span_singleton n hS hcont u residual⟩

/-- Continuing-branch displayed source-chart frontier payload.

This is the next same-stage lower-row product package together with the
finite nonemptiness of the next residual center. -/
abbrev ContinuingSourceChartFrontierPayload
    {τ R : Type*} [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (t : ℕ → ℕ → ℕ → ℤ)
    (numerator leastValue : ℕ → ℕ → ℤ)
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (u : R) (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (C : ℕ → τ → R) : Prop :=
  (case2ResidualBlockPivotEntries n S (J + 1)).Nonempty ∧
    (case2DisplayedPaperDppp n hS hcont residual *
        case2DisplayedPaperCprime n hS hcont residual C).submatrix
        (fun i ↦
          Sum.inr
            ((case2DisplayedPivotRowComplementEquivResidualRowSucc
              n hS hcont).symm i))
        id =
      case2DisplayedPostPivotResidualBlock n hS hcont residual *
        case2SourceFollowingFactor (n := n) (S := S) (J := J + 1) C ∧
    IntroducedLabelExponentCertificates L n S (J + 1)
      (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
      (updateSelectedLabelScalar S (J + 1)
        (((prefixMinNat n S : ℤ) - (J : ℤ)) *
          ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    IntroducedLabelLevelInvariants L n S (J + 1)
      ((pre.case2Succ
        (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))).level)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    case2IntroducedLabelLeastValueGap L n S (J + 1)
      (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
    (pre.case2Succ
      (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1))).case2Gap

/-- Actual-width stopped displayed source-chart frontier payload with a supplied
following factor and finite center principalization. -/
abbrev ActualWidthSourceChartFrontierPayload
    {υ τ R : Type*} [CommRing R] [Fintype τ]
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (t : ℕ → ℕ → ℕ → ℤ)
    (numerator leastValue : ℕ → ℕ → ℤ)
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (u : R) (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (C : ℕ → τ → R) (F : Matrix τ υ R) : Prop :=
  (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
    matrixEntryIdeal
        ((fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
            (weightedPivotBlockRowOp q
                  (fun i ↦
                    pivotFirstX
                      (case2DisplayedPivotRow n hS hcont)
                      (case2DisplayedPivotCol n hS hcont)
                      (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                  case2DisplayedSourceSubstitutionBlock n hS hcont
                    (case2DisplayedSourceChartMap n hS hcont u residual
                      (J + 1, J + 1)) residual).submatrix
                  (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                  (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
            verticalBlock (case2DisplayedSourceOldTopBlock C)
              (case2DisplayedSourceFollowingFactor n hS hcont C)) * F) =
    matrixEntryIdeal
        ((case2DisplayedSourceTerminalWeight
            (case2DisplayedSourceOldTopWeight pre)
            ((pre.case2Succ
              (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
              |>.stageRelabelSuccZero
              |>.weight (J + 1)) *
          case2DisplayedSourceTerminalOriginalRows C) * F)) ∧
  IntroducedLabelLevelInvariants L n (S + 1) 0
    ((pre.case2Succ
      (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
      |>.stageRelabelSuccZero
      |>.level)
    (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
  IntroducedLabelExponentCertificates L n (S + 1) 0
    (updateSelectedLabelVector S (J + 1) (correctedCase2PivotVector n S J) t)
    (updateSelectedLabelScalar S (J + 1)
      (((prefixMinNat n S : ℤ) - (J : ℤ)) *
        ((n (S + 1) : ℤ) - (J : ℤ))) numerator)
    (updateSelectedLabelScalar S (J + 1) (J : ℤ) leastValue) ∧
  u ∈
    {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
      case2DisplayedSourceChartMap n hS hcont u residual p = v} ∧
  (∀ p, p ∈ case2ResidualBlockPivotEntries n S J →
    u ∣ case2DisplayedSourceChartMap n hS hcont u residual p) ∧
  Ideal.span
      {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        case2DisplayedSourceChartMap n hS hcont u residual p = v} =
    Ideal.span ({u} : Set R)

/-- Row-exhausted terminal-last displayed source-chart frontier payload with
transported prefix rows and finite center principalization. -/
abbrev RowExhaustedTerminalLastSourceChartFrontierPayload
    {R : Type*} [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (u : R) (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hrow : prefixMinNat n S = J + 1)
    (κ : Fin (L + 1) → Type*) [∀ i, Finite (κ i)]
    (hSuffix : S + 1 ≤ L)
    (C : ℕ → κ (sourceLayerIndex L (S + 2)
      (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R) :
    Prop :=
  (∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
    matrixEntryIdeal
        (fromBlocks (case2DisplayedSourceOldTopWeight pre) 0 0
            (weightedPivotBlockRowOp q
                  (fun i ↦
                    pivotFirstX
                      (case2DisplayedPivotRow n hS hcont)
                      (case2DisplayedPivotCol n hS hcont)
                      (case2DisplayedPaperDchart n hS hcont residual) i ()) *
                (diagonal (fun i ↦ pre.case2ResidualRowWeight i) *
                  case2DisplayedSourceSubstitutionBlock n hS hcont
                    (case2DisplayedSourceChartMap n hS hcont u residual
                      (J + 1, J + 1)) residual).submatrix
                  (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
                  (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
            verticalBlock (case2DisplayedSourceOldTopBlock C)
              (case2DisplayedSourceFollowingFactor n hS hcont C)) =
    matrixEntryIdeal
        (case2DisplayedSourceTerminalWeightPrefixCandidate
            (case2DisplayedSourceOldTopWeight pre)
            n hcont
            (case2_not_next_cont_of_prefixMin_current_eq hS hrow)
            ((pre.case2Succ
              (case2DisplayedSourceChartMap n hS hcont u residual (J + 1, J + 1)))
              |>.weight (J + 1)) *
          (case2DisplayedSourceTerminalTransportedRows n hS hcont residual C).submatrix
            (case2SourceTerminalRowEquivPrefixOfNotNext n hcont
              (case2_not_next_cont_of_prefixMin_current_eq hS hrow)).symm id)) ∧
  u ∈
    {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
      case2DisplayedSourceChartMap n hS hcont u residual p = v} ∧
  (∀ p, p ∈ case2ResidualBlockPivotEntries n S J →
    u ∣ case2DisplayedSourceChartMap n hS hcont u residual p) ∧
  Ideal.span
      {v : R | ∃ p, p ∈ case2ResidualBlockPivotEntries n S J ∧
        case2DisplayedSourceChartMap n hS hcont u residual p = v} =
    Ideal.span ({u} : Set R)

/-- Fielded implication bundle for the displayed Case 2 source-chart frontier.

The fields expose existing consequences under explicit branch hypotheses
`hnext`, `hwidth`, and `hrow`.  The stopped alternatives may overlap, and this
structure does not choose a unique semantic branch.  It is branch-domain and
supplied-boundary bookkeeping only; it does not produce charts, post-data,
terminal source data, transition invariance, normal crossings, pole order, or
RLCT consequences. -/
structure SourceChartFrontierBoundaryPackages
    (R : Type*) [CommRing R]
    (L : ℕ) (n : ℕ → ℕ) (S J : ℕ)
    (t : ℕ → ℕ → ℕ → ℤ)
    (numerator leastValue : ℕ → ℕ → ℤ)
    (pre : IntroducedLabelRecurrenceState L n S J R)
    (u : R) (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hcont : J + 1 ≤ prefixMinNat n (S + 1)) : Prop where
  frontierBranch : Case2DisplayedStepBranch n S J
  continuing :
    ∀ {τ : Type*} (C : ℕ → τ → R),
      J + 2 ≤ prefixMinNat n (S + 1) →
        ContinuingSourceChartFrontierPayload
          L n S J t numerator leastValue pre u residual hS hcont C
  actualWidthStopped :
    ∀ {υ τ : Type*} [Fintype τ] (C : ℕ → τ → R) (F : Matrix τ υ R),
      n (S + 1) = J + 1 →
        ActualWidthSourceChartFrontierPayload
          L n S J t numerator leastValue pre u residual hS hcont C F
  rowExhaustedStopped :
    ∀ (κ : Fin (L + 1) → Type*) [∀ i, Finite (κ i)]
      (hSuffix : S + 1 ≤ L) (_hLast : S + 1 = L)
      (C : ℕ → κ (sourceLayerIndex L (S + 2)
        (Nat.succ_le_succ (Nat.zero_le (S + 1))) (Nat.succ_le_succ hSuffix)) → R)
      (_Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R),
      (hrow : prefixMinNat n S = J + 1) →
        RowExhaustedTerminalLastSourceChartFrontierPayload
          L n S J pre u residual hS hcont hrow κ hSuffix C

/-- Concrete displayed source-chart frontier implication package.

This packages existing branch-specific boundary theorems as implications under
their explicit branch hypotheses.  It does not assert that the branch
hypotheses are exclusive, and it does not identify the row-exhausted branch
with actual-width terminal relabeling. -/
theorem sourceChartMap_frontierBoundaryPackages
    {R : Type*} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState L n S J R) (u : R)
    (residual : ℕ × ℕ → R)
    (hS : 1 ≤ S) (hSL : S ≤ L)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants L n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap L n S J leastValue)
    {ChartRegular : ℕ × ℕ → Prop}
    {TransitionRegular : ℕ × ℕ → ℕ × ℕ → Prop}
    (chartFamily :
      Case2ResidualBlockChartFamilyBoundary n S J ChartRegular TransitionRegular) :
    SourceChartFrontierBoundaryPackages R L n S J t numerator leastValue
      pre u residual hS hcont where
  frontierBranch := case2DisplayedStepBranch_of_cont hS hcont
  continuing := by
    intro τ C hnext
    exact
      ⟨case2DisplayedPostPivotResidualBlock_nonempty_of_next n hS hnext,
        sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData
          pre u residual hS hSL hcont exponentPre levelInv leastValueGap
          chartFamily C⟩
  actualWidthStopped := by
    intro υ τ inst C F hwidth
    exact
      sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal
        pre u residual hS hSL hcont hwidth exponentPre levelInv leastValueGap
        chartFamily C F
  rowExhaustedStopped := by
    intro κ inst hSuffix hLast C Ctail hrow
    exact
      sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal
        pre u residual hS hSL hcont hrow exponentPre levelInv leastValueGap
        chartFamily κ hSuffix hLast C Ctail

end Case2DisplayedSuppliedChartFamilyBoundary

/-- Displayed Case 2 `Q/P` identity when row weights are a monomial recurrence
indexed by the residual source row. This supplies quotient witnesses from the
row-index lower bound; it is still only local finite algebra. -/
theorem exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec
    (step : ℕ → R) (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      (weightedPivotBlockRowOp q
          (fun i ↦
            pivotFirstX
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
          weightedPivotDiagonal
            (u * monomialRec step (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * monomialRec step (case2ResidualRowLevel n S J i.1)) *
          pivotFirstMatrix
            (case2DisplayedPivotRow n hS hcont)
            (case2DisplayedPivotCol n hS hcont)
            (case2DisplayedNormalizedMatrix n hS hcont residual)) *
          case2DisplayedFollowingFactor n hS hcont C =
        (weightedPivotDiagonal
            (u * monomialRec step (J + 1))
            (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
              u * monomialRec step (case2ResidualRowLevel n S J i.1)) *
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
          case2DisplayedTransportedFollowingFactor n hS hcont residual C := by
  simpa [case2DisplayedTransportedFollowingFactor, case2DisplayedNormalizedMatrix,
      case2DisplayedFollowingFactor] using
    exists_pivotFirstQP_mul_of_pivotMul_monomialRec_eq_or_le
      (R := R) step u
      (rowPivot := case2DisplayedPivotRow n hS hcont)
      (colPivot := case2DisplayedPivotCol n hS hcont)
      (a := J + 1)
      (level := fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
        case2ResidualRowLevel n S J i.1)
      (A := case2DisplayedNormalizedMatrix n hS hcont residual)
      (selectedEntryNormalizedMatrix_pivot
        (case2DisplayedPivotRow n hS hcont)
        (case2DisplayedPivotCol n hS hcont) residual)
      (C := case2DisplayedFollowingFactor n hS hcont C)
      (fun i ↦ Or.inr (case2ResidualRowLevel_ge n S J i.1))

/-- Displayed Case 2 source-substitution tail identity lifted through an
unchanged top block.  This is block-diagonal bookkeeping for the displayed
pivot chart, not arbitrary-pivot coverage or a full transition theorem. -/
theorem exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_flat_weights
    {ι : Type*} [Fintype ι]
    (Atop : Matrix ι ι R) (Ctop : Matrix ι τ R)
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (u : R) (weight : Case2ResidualRowIndex n S J → R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R)
    (hflat : ∀ i, weight i = weight (case2DisplayedPivotRow n hS hcont)) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      fromBlocks Atop 0 0
          (weightedPivotBlockRowOp q
              (fun i ↦
                pivotFirstX
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont)
                  (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
            (diagonal weight *
              case2DisplayedSubstitutionMatrix n hS hcont u residual).submatrix
              (pivotFirstIndexEquiv (case2DisplayedPivotRow n hS hcont))
              (pivotFirstIndexEquiv (case2DisplayedPivotCol n hS hcont))) *
          verticalBlock Ctop (case2DisplayedFollowingFactor n hS hcont C) =
        fromBlocks Atop 0 0
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
          verticalBlock Ctop
            (case2DisplayedTransportedFollowingFactor n hS hcont residual C) := by
  rcases exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights
      n hS hcont u weight residual C hflat with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  exact fromBlocks_mul_verticalBlock_eq_of_tail Atop _ _ Ctop _ _
    (by simpa [case2DisplayedTransportedFollowingFactor] using hq)

/-- Displayed Case 2 row-index recurrence tail identity lifted through an
unchanged top block.  The row weights are assumed to already have the
`u * monomialRec step rowLevel` form. -/
theorem exists_case2DisplayedQP_verticalBlock_transportedFollowingFactor_of_rowIndex_monomialRec
    {ι : Type*} [Fintype ι]
    (Atop : Matrix ι ι R) (Ctop : Matrix ι τ R)
    (step : ℕ → R) (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) (u : R)
    (residual : Case2ResidualRowIndex n S J → Case2ResidualColIndex n S J → R)
    (C : Matrix (Case2ResidualColIndex n S J) τ R) :
    ∃ q : pivotComplement (case2DisplayedPivotRow n hS hcont) → R,
      fromBlocks Atop 0 0
          (weightedPivotBlockRowOp q
              (fun i ↦
                pivotFirstX
                  (case2DisplayedPivotRow n hS hcont)
                  (case2DisplayedPivotCol n hS hcont)
                  (case2DisplayedNormalizedMatrix n hS hcont residual) i ()) *
            weightedPivotDiagonal
              (u * monomialRec step (J + 1))
              (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
                u * monomialRec step (case2ResidualRowLevel n S J i.1)) *
            pivotFirstMatrix
              (case2DisplayedPivotRow n hS hcont)
              (case2DisplayedPivotCol n hS hcont)
              (case2DisplayedNormalizedMatrix n hS hcont residual)) *
          verticalBlock Ctop (case2DisplayedFollowingFactor n hS hcont C) =
        fromBlocks Atop 0 0
          (weightedPivotDiagonal
              (u * monomialRec step (J + 1))
              (fun i : pivotComplement (case2DisplayedPivotRow n hS hcont) ↦
                u * monomialRec step (case2ResidualRowLevel n S J i.1)) *
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
          verticalBlock Ctop
            (case2DisplayedTransportedFollowingFactor n hS hcont residual C) := by
  rcases exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec
      step n hS hcont u residual C with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  exact fromBlocks_mul_verticalBlock_eq_of_tail Atop _ _ Ctop _ _ hq

end ColumnOperationBlocks

end Aoyagi
end DLN
end DLNFibre
