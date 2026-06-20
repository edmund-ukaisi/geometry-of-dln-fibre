import DLNFibre.DLN.Aoyagi.Lemma4CountArithmetic
import DLNFibre.DLN.Aoyagi.Lemma5IntervalArithmetic

/-!
# Arithmetic for Aoyagi's displayed `Htilde` chains

This file isolates the finite arithmetic of Aoyagi's two displayed extremal
`H`-chains around Lemma 4 and Lemma 5.  It does not prove exponent-vector
admissibility, chart coverage, pole order, normal crossings, or RLCT extraction.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- A selected width sequence, extended by zero outside its source range. -/
def aoyagiSelectedWidthNat (ell : ℕ) (m : Fin (ell + 1) → ℤ) (i : ℕ) : ℤ :=
  if h : i < ell + 1 then m ⟨i, h⟩ else 0

/-- Prefix sum `w_0+...+w_j`, matching Aoyagi's `P_(j+1)` under zero-based
selected-width indexing. -/
def aoyagiPrefixSum (w : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (j + 1), w i

@[simp] theorem aoyagiSelectedWidthNat_of_lt
    {ell : ℕ} {m : Fin (ell + 1) → ℤ} {i : ℕ} (h : i < ell + 1) :
    aoyagiSelectedWidthNat ell m i = m ⟨i, h⟩ := by
  simp [aoyagiSelectedWidthNat, h]

@[simp] theorem aoyagiSelectedWidthNat_zero (ell : ℕ) (m : Fin (ell + 1) → ℤ) :
    aoyagiSelectedWidthNat ell m 0 = m 0 := by
  simp [aoyagiSelectedWidthNat]

@[simp] theorem aoyagiSelectedWidthNat_succ_fin
    {ell : ℕ} (m : Fin (ell + 1) → ℤ) (j : Fin ell) :
    aoyagiSelectedWidthNat ell m (j.val + 1) = m j.succ := by
  unfold aoyagiSelectedWidthNat
  split
  · exact congrArg m (Fin.ext rfl)
  · omega

@[simp] theorem aoyagiPrefixSum_zero (w : ℕ → ℤ) :
    aoyagiPrefixSum w 0 = w 0 := by
  simp [aoyagiPrefixSum]

/-- Successor rule for the inclusive prefix sum. -/
theorem aoyagiPrefixSum_succ (w : ℕ → ℤ) (j : ℕ) :
    aoyagiPrefixSum w (j + 1) = aoyagiPrefixSum w j + w (j + 1) := by
  unfold aoyagiPrefixSum
  rw [Finset.sum_range_succ]

/-- The terminal selected-width prefix sum is the original finite sum. -/
theorem aoyagiPrefixSum_selectedWidthNat_last (ell : ℕ) (m : Fin (ell + 1) → ℤ) :
    aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) ell =
      ∑ i : Fin (ell + 1), m i := by
  unfold aoyagiPrefixSum
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  exact aoyagiSelectedWidthNat_of_lt i.isLt

/-- Prefix count of high increments for the lower `Htilde` chain. -/
def aoyagiHtildeLowerHighCount (a j : ℕ) : ℕ :=
  min j a

/-- Prefix count of high increments for the upper `Htilde'` chain. -/
def aoyagiHtildeUpperHighCount (ell a j : ℕ) : ℕ :=
  min a (j - (ell - a))

/-- Amount subtracted from the selected-width prefix in the lower chain. -/
def aoyagiHtildeLowerIncrementPrefix (a : ℕ) (M : ℤ) (j : ℕ) : ℤ :=
  (j : ℤ) * (M - 1) + (aoyagiHtildeLowerHighCount a j : ℤ)

/-- Amount subtracted from the selected-width prefix in the upper chain. -/
def aoyagiHtildeUpperIncrementPrefix (ell a : ℕ) (M : ℤ) (j : ℕ) : ℤ :=
  (j : ℤ) * (M - 1) + (aoyagiHtildeUpperHighCount ell a j : ℤ)

/-- Aoyagi's lower displayed `Htilde` chain, extended to the `j=0` convention. -/
def aoyagiHtildeLowerNat (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (j : ℕ) : ℤ :=
  aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) j -
    aoyagiHtildeLowerIncrementPrefix a M j

/-- Aoyagi's upper displayed `Htilde'` chain, extended to the `j=0` convention. -/
def aoyagiHtildeUpperNat (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (j : ℕ) : ℤ :=
  aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) j -
    aoyagiHtildeUpperIncrementPrefix ell a M j

/-- Finite-indexed lower `Htilde` chain. -/
def aoyagiHtildeLowerChain (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) : Fin (ell + 1) → ℤ :=
  fun j ↦ aoyagiHtildeLowerNat ell a M m j.val

/-- Finite-indexed upper `Htilde'` chain. -/
def aoyagiHtildeUpperChain (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) : Fin (ell + 1) → ℤ :=
  fun j ↦ aoyagiHtildeUpperNat ell a M m j.val

/-- Both chains begin at the source convention `H_0=M(S_1)`. -/
theorem aoyagiHtildeLowerChain_zero (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) :
    aoyagiHtildeLowerChain ell a M m 0 = m 0 := by
  simp [aoyagiHtildeLowerChain, aoyagiHtildeLowerNat,
    aoyagiHtildeLowerIncrementPrefix, aoyagiHtildeLowerHighCount]

/-- Both chains begin at the source convention `H_0=M(S_1)`. -/
theorem aoyagiHtildeUpperChain_zero (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) :
    aoyagiHtildeUpperChain ell a M m 0 = m 0 := by
  simp [aoyagiHtildeUpperChain, aoyagiHtildeUpperNat,
    aoyagiHtildeUpperIncrementPrefix, aoyagiHtildeUpperHighCount]

/-- The lower-chain subtraction changes by `M` for the first `a` increments,
and by `M-1` afterwards. -/
theorem aoyagiHtildeLowerIncrementPrefix_succ_sub (a : ℕ) (M : ℤ) (j : ℕ) :
    aoyagiHtildeLowerIncrementPrefix a M (j + 1) -
        aoyagiHtildeLowerIncrementPrefix a M j =
      if j < a then M else M - 1 := by
  unfold aoyagiHtildeLowerIncrementPrefix aoyagiHtildeLowerHighCount
  by_cases hj : j < a
  · have hmin_j : min j a = j := Nat.min_eq_left (Nat.le_of_lt hj)
    have hmin_succ : min (j + 1) a = j + 1 := Nat.min_eq_left (by omega)
    rw [hmin_j, hmin_succ]
    simp [hj]
    ring
  · have hmin_j : min j a = a := Nat.min_eq_right (by omega)
    have hmin_succ : min (j + 1) a = a := Nat.min_eq_right (by omega)
    rw [hmin_j, hmin_succ]
    simp [hj]
    ring

/-- The upper-chain subtraction changes by `M-1` for the first `ell-a`
increments, and by `M` afterwards. -/
theorem aoyagiHtildeUpperIncrementPrefix_succ_sub (ell a : ℕ) (M : ℤ) (j : ℕ)
    (ha : a ≤ ell) (hjell : j < ell) :
    aoyagiHtildeUpperIncrementPrefix ell a M (j + 1) -
        aoyagiHtildeUpperIncrementPrefix ell a M j =
      if j < ell - a then M - 1 else M := by
  unfold aoyagiHtildeUpperIncrementPrefix aoyagiHtildeUpperHighCount
  by_cases hj : j < ell - a
  · have hsub_j : j - (ell - a) = 0 := by omega
    have hsub_succ : (j + 1) - (ell - a) = 0 := by omega
    simp [hj, hsub_j, hsub_succ]
    ring
  · have hsub_j_le : j - (ell - a) ≤ a := by omega
    have hsub_succ_le : (j + 1) - (ell - a) ≤ a := by omega
    have hmin_j : min a (j - (ell - a)) = j - (ell - a) :=
      Nat.min_eq_right hsub_j_le
    have hmin_succ : min a ((j + 1) - (ell - a)) = (j + 1) - (ell - a) :=
      Nat.min_eq_right hsub_succ_le
    simp [hj, hmin_j, hmin_succ]
    ring_nf
    omega

/-- The lower chain has the common terminal endpoint displayed in Lemma 4. -/
theorem aoyagiHtildeLowerChain_last_eq_terminalEndpoint (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell) :
    aoyagiHtildeLowerChain ell a M m (Fin.last ell) =
      aoyagiLemma4TerminalEndpoint ell a M m := by
  have hsum := aoyagiPrefixSum_selectedWidthNat_last ell m
  have hmin : min ell a = a := Nat.min_eq_right ha
  unfold aoyagiHtildeLowerChain aoyagiHtildeLowerNat
    aoyagiHtildeLowerIncrementPrefix aoyagiHtildeLowerHighCount
    aoyagiLemma4TerminalEndpoint
  simp only [Fin.val_last]
  change aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) ell -
      ((ell : ℤ) * (M - 1) + ((min ell a : ℕ) : ℤ)) =
    (∑ j : Fin (ell + 1), m j) -
      ((a : ℤ) * M + ((ell - a : ℕ) : ℤ) * (M - 1))
  rw [hsum, hmin, Nat.cast_sub ha]
  ring

/-- The upper chain has the common terminal endpoint displayed in Lemma 4. -/
theorem aoyagiHtildeUpperChain_last_eq_terminalEndpoint (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell) :
    aoyagiHtildeUpperChain ell a M m (Fin.last ell) =
      aoyagiLemma4TerminalEndpoint ell a M m := by
  have hsum := aoyagiPrefixSum_selectedWidthNat_last ell m
  have hsub : ell - (ell - a) = a := by omega
  have hmin : min a (ell - (ell - a)) = a := by simp [hsub]
  unfold aoyagiHtildeUpperChain aoyagiHtildeUpperNat
    aoyagiHtildeUpperIncrementPrefix aoyagiHtildeUpperHighCount
    aoyagiLemma4TerminalEndpoint
  simp only [Fin.val_last]
  change aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) ell -
      ((ell : ℤ) * (M - 1) + ((min a (ell - (ell - a)) : ℕ) : ℤ)) =
    (∑ j : Fin (ell + 1), m j) -
      ((a : ℤ) * M + ((ell - a : ℕ) : ℤ) * (M - 1))
  rw [hsum, hmin, Nat.cast_sub ha]
  ring

/-- The lower chain realizes the high-first ordered increment pattern. -/
theorem aoyagiHtildeLowerChain_F_eq (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (j : Fin ell) :
    aoyagiLemma4F ell m (aoyagiHtildeLowerChain ell a M m) j =
      if (j : ℕ) < a then M else M - 1 := by
  let w := aoyagiSelectedWidthNat ell m
  let P := aoyagiPrefixSum w
  let A := aoyagiHtildeLowerIncrementPrefix a M
  have hprefix : P (j.val + 1) = P j.val + m j.succ := by
    dsimp [P, w]
    rw [aoyagiPrefixSum_succ]
    rw [aoyagiSelectedWidthNat_succ_fin m j]
  have hcalc : (P j.val - A j.val) - (P (j.val + 1) - A (j.val + 1)) +
        m j.succ = A (j.val + 1) - A j.val := by
    rw [hprefix]
    ring
  change (P j.val - A j.val) - (P (j.val + 1) - A (j.val + 1)) +
      m j.succ = if (j : ℕ) < a then M else M - 1
  rw [hcalc]
  exact aoyagiHtildeLowerIncrementPrefix_succ_sub a M j.val

/-- The upper chain realizes the low-first ordered increment pattern. -/
theorem aoyagiHtildeUpperChain_F_eq (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell) (j : Fin ell) :
    aoyagiLemma4F ell m (aoyagiHtildeUpperChain ell a M m) j =
      if (j : ℕ) < ell - a then M - 1 else M := by
  let w := aoyagiSelectedWidthNat ell m
  let P := aoyagiPrefixSum w
  let A := aoyagiHtildeUpperIncrementPrefix ell a M
  have hprefix : P (j.val + 1) = P j.val + m j.succ := by
    dsimp [P, w]
    rw [aoyagiPrefixSum_succ]
    rw [aoyagiSelectedWidthNat_succ_fin m j]
  have hcalc : (P j.val - A j.val) - (P (j.val + 1) - A (j.val + 1)) +
        m j.succ = A (j.val + 1) - A j.val := by
    rw [hprefix]
    ring
  change (P j.val - A j.val) - (P (j.val + 1) - A (j.val + 1)) +
      m j.succ = if (j : ℕ) < ell - a then M - 1 else M
  rw [hcalc]
  exact aoyagiHtildeUpperIncrementPrefix_succ_sub ell a M j.val ha j.isLt

/-- The high-count gap between the upper and lower chains is Aoyagi's interval
excess formula. -/
theorem aoyagiHtildeHighCount_diff_eq_intervalExcess
    {ell a j : ℕ} (ha : a ≤ ell) (hj : j ≤ ell) :
    ((aoyagiHtildeLowerHighCount a j : ℤ) -
      (aoyagiHtildeUpperHighCount ell a j : ℤ)) =
        (aoyagiLemma5IntervalExcess ell a j : ℤ) := by
  unfold aoyagiHtildeLowerHighCount aoyagiHtildeUpperHighCount
    aoyagiLemma5IntervalExcess
  by_cases hja : j ≤ a
  · by_cases hjc : j ≤ ell - a
    · have hmin_ja : min j a = j := Nat.min_eq_left hja
      have hsub : j - (ell - a) = 0 := by omega
      have hmin_excess : min j (min (ell - j) (min a (ell - a))) = j := by
        apply Nat.min_eq_left
        exact Nat.le_min.mpr ⟨by omega, Nat.le_min.mpr ⟨hja, hjc⟩⟩
      simp [hmin_ja, hsub, hmin_excess]
    · have hmin_ja : min j a = j := Nat.min_eq_left hja
      have hsub_le : j - (ell - a) ≤ a := by omega
      have hmin_high : min a (j - (ell - a)) = j - (ell - a) :=
        Nat.min_eq_right hsub_le
      have hmin_ac : min a (ell - a) = ell - a := Nat.min_eq_right (by omega)
      have hmin_excess : min j (min (ell - j) (min a (ell - a))) = ell - a := by
        rw [hmin_ac]
        have hinner : min (ell - j) (ell - a) = ell - a :=
          Nat.min_eq_right (by omega)
        rw [hinner]
        exact Nat.min_eq_right (by omega)
      simp [hmin_ja, hmin_high, hmin_excess]
      omega
  · by_cases hjc : j ≤ ell - a
    · have hmin_ja : min j a = a := Nat.min_eq_right (by omega)
      have hsub : j - (ell - a) = 0 := by omega
      have hmin_ac : min a (ell - a) = a := Nat.min_eq_left (by omega)
      have hmin_excess : min j (min (ell - j) (min a (ell - a))) = a := by
        rw [hmin_ac]
        have hinner : min (ell - j) a = a := Nat.min_eq_right (by omega)
        rw [hinner]
        exact Nat.min_eq_right (by omega)
      simp [hmin_ja, hsub, hmin_excess]
    · have hmin_ja : min j a = a := Nat.min_eq_right (by omega)
      have hsub_le : j - (ell - a) ≤ a := by omega
      have hmin_high : min a (j - (ell - a)) = j - (ell - a) :=
        Nat.min_eq_right hsub_le
      have hmin_excess : min j (min (ell - j) (min a (ell - a))) = ell - j := by
        have hinner : min (ell - j) (min a (ell - a)) = ell - j := by
          apply Nat.min_eq_left
          exact Nat.le_min.mpr ⟨by omega, by omega⟩
        rw [hinner]
        exact Nat.min_eq_right (by omega)
      simp [hmin_ja, hmin_high, hmin_excess]
      omega

/-- The pointwise gap between the two displayed chains is the Lemma 5 interval
excess. -/
theorem aoyagiHtildeUpper_sub_lower_eq_intervalExcess
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (j : Fin (ell + 1)) :
    aoyagiHtildeUpperChain ell a M m j -
      aoyagiHtildeLowerChain ell a M m j =
        (aoyagiLemma5IntervalExcess ell a j.val : ℤ) := by
  have hgap := aoyagiHtildeHighCount_diff_eq_intervalExcess
    (ell := ell) (a := a) (j := j.val) ha (by omega)
  unfold aoyagiHtildeUpperChain aoyagiHtildeLowerChain
    aoyagiHtildeUpperNat aoyagiHtildeLowerNat
    aoyagiHtildeUpperIncrementPrefix aoyagiHtildeLowerIncrementPrefix
  omega

/-- The displayed lower chain has zero terminal value under Definition 3's
selected-width sum. -/
theorem aoyagiHtildeLowerChain_last_eq_zero_of_selectedSum (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    aoyagiHtildeLowerChain ell a M m (Fin.last ell) = 0 := by
  rw [aoyagiHtildeLowerChain_last_eq_terminalEndpoint ell a M m ha]
  exact aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum ell a M m ha hselected

/-- The displayed upper chain has zero terminal value under Definition 3's
selected-width sum. -/
theorem aoyagiHtildeUpperChain_last_eq_zero_of_selectedSum (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    aoyagiHtildeUpperChain ell a M m (Fin.last ell) = 0 := by
  rw [aoyagiHtildeUpperChain_last_eq_terminalEndpoint ell a M m ha]
  exact aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum ell a M m ha hselected

/-- The displayed lower chain is pointwise below the displayed upper chain.

This is a same-coordinate statement about the finite `H`-chains.  It is not a
proof that Aoyagi's componentwise order on exponent vectors induces these
chain-coordinate inequalities. -/
theorem aoyagiHtildeLowerChain_le_upperChain (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell) :
    aoyagiHtildeLowerChain ell a M m ≤ aoyagiHtildeUpperChain ell a M m := by
  intro j
  have hgap := aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m ha j
  have hnonneg : 0 ≤ (aoyagiLemma5IntervalExcess ell a j.val : ℤ) := by
    exact_mod_cast Nat.zero_le (aoyagiLemma5IntervalExcess ell a j.val)
  have hdiff :
      0 ≤ aoyagiHtildeUpperChain ell a M m j -
        aoyagiHtildeLowerChain ell a M m j := by
    rw [hgap]
    exact hnonneg
  exact sub_nonneg.mp hdiff

/-- Offsets from the lower displayed chain to the upper displayed chain at
the `j`th chain coordinate. -/
def aoyagiHtildeIntervalOffsets (ell a j : ℕ) : Finset ℕ :=
  Finset.Icc 0 (aoyagiLemma5IntervalExcess ell a j)

/-- The offset interval has Aoyagi's displayed Lemma 5 interval size. -/
theorem aoyagiHtildeIntervalOffsets_card (ell a j : ℕ) :
    (aoyagiHtildeIntervalOffsets ell a j).card =
      aoyagiLemma5IntervalSize ell a j := by
  unfold aoyagiHtildeIntervalOffsets aoyagiLemma5IntervalSize
  rw [Nat.card_Icc]
  omega

/-- The finite set of same-coordinate integer values between the two
displayed `Htilde` chains at coordinate `j`. -/
def aoyagiHtildeIntervalValueSet (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (j : Fin (ell + 1)) : Finset ℤ :=
  (aoyagiHtildeIntervalOffsets ell a j.val).image
    (fun r : ℕ ↦ aoyagiHtildeLowerChain ell a M m j + (r : ℤ))

/-- Membership in the same-coordinate value set is exactly being between the
two displayed `Htilde` chain values. -/
theorem aoyagiHtilde_mem_intervalValueSet_iff_bounds
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (j : Fin (ell + 1)) (Hj : ℤ) :
    Hj ∈ aoyagiHtildeIntervalValueSet ell a M m j ↔
      aoyagiHtildeLowerChain ell a M m j ≤ Hj ∧
        Hj ≤ aoyagiHtildeUpperChain ell a M m j := by
  constructor
  · intro hmem
    rw [aoyagiHtildeIntervalValueSet, Finset.mem_image] at hmem
    rcases hmem with ⟨r, hr, rfl⟩
    rw [aoyagiHtildeIntervalOffsets, Finset.mem_Icc] at hr
    have hgap :=
      aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m ha j
    constructor
    · omega
    · omega
  · intro hbounds
    rw [aoyagiHtildeIntervalValueSet, Finset.mem_image]
    let r : ℕ := Int.toNat (Hj - aoyagiHtildeLowerChain ell a M m j)
    have hr_cast : (r : ℤ) =
        Hj - aoyagiHtildeLowerChain ell a M m j := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hbounds.1)
    have hgap :=
      aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m ha j
    have hr_le_int : (r : ℤ) ≤ (aoyagiLemma5IntervalExcess ell a j.val : ℤ) := by
      omega
    have hr_le_nat : r ≤ aoyagiLemma5IntervalExcess ell a j.val := by
      exact_mod_cast hr_le_int
    refine ⟨r, ?_, ?_⟩
    · rw [aoyagiHtildeIntervalOffsets, Finset.mem_Icc]
      exact ⟨Nat.zero_le r, hr_le_nat⟩
    · omega

/-- The same-coordinate value set has Aoyagi's displayed Lemma 5 interval
size. -/
theorem aoyagiHtildeIntervalValueSet_card
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) (j : Fin (ell + 1)) :
    (aoyagiHtildeIntervalValueSet ell a M m j).card =
      aoyagiLemma5IntervalSize ell a j.val := by
  unfold aoyagiHtildeIntervalValueSet
  rw [Finset.card_image_of_injOn]
  · exact aoyagiHtildeIntervalOffsets_card ell a j.val
  · intro x _ y _ hxy
    have hcast : (x : ℤ) = (y : ℤ) := by
      exact add_left_cancel hxy
    exact_mod_cast hcast

/-- Same-coordinate chain bounds put every intermediate `H_j` in the finite
interval value set. -/
theorem aoyagiHtildeChainBounds_mem_intervalValueSet
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell)
    (hlower : aoyagiHtildeLowerChain ell a M m ≤ H)
    (hupper : H ≤ aoyagiHtildeUpperChain ell a M m) :
    ∀ j, H j ∈ aoyagiHtildeIntervalValueSet ell a M m j := by
  intro j
  rw [aoyagiHtilde_mem_intervalValueSet_iff_bounds ell a M m ha j (H j)]
  exact ⟨hlower j, hupper j⟩

/-- Componentwise vector bounds imply finite interval membership once a
same-coordinate chain map is supplied.

This is a conservative API.  It assumes the coordinate map from chain positions
to vector coordinates; it does not derive that map from Aoyagi's Definition 4. -/
theorem aoyagiHtilde_interval_mem_of_sameCoordinateChain
    {ι : Type*} (ell a : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ) (coord : Fin (ell + 1) → ι)
    {Tlo T Thi : ι → ℤ}
    (ha : a ≤ ell) (hlo : Tlo ≤ T) (hhi : T ≤ Thi)
    (hlo_coord : ∀ j, Tlo (coord j) = aoyagiHtildeLowerChain ell a M m j)
    (hH_coord : ∀ j, T (coord j) = H j)
    (hhi_coord : ∀ j, Thi (coord j) = aoyagiHtildeUpperChain ell a M m j) :
    ∀ j, H j ∈ aoyagiHtildeIntervalValueSet ell a M m j := by
  intro j
  rw [aoyagiHtilde_mem_intervalValueSet_iff_bounds ell a M m ha j (H j)]
  constructor
  · rw [← hlo_coord j, ← hH_coord j]
    exact hlo (coord j)
  · rw [← hH_coord j, ← hhi_coord j]
    exact hhi (coord j)

/-- If an intermediate `H`-chain is squeezed between the two displayed
`Htilde` chains in the same coordinates, then its terminal value is zero.

This is the honest chain-coordinate replacement for the source sentence using
`Ttilde <= T <= Ttilde'`.  The vector-to-chain coordinate correspondence is
not proved here. -/
theorem aoyagiLemma4_Hlast_eq_zero_of_HtildeChainBounds (ell a : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hlower : aoyagiHtildeLowerChain ell a M m ≤ H)
    (hupper : H ≤ aoyagiHtildeUpperChain ell a M m) :
    H (Fin.last ell) = 0 := by
  have hlo0 := aoyagiHtildeLowerChain_last_eq_zero_of_selectedSum ell a M m ha hselected
  have hhi0 := aoyagiHtildeUpperChain_last_eq_zero_of_selectedSum ell a M m ha hselected
  have hlo := hlower (Fin.last ell)
  have hhi := hupper (Fin.last ell)
  have hlo' : (0 : ℤ) ≤ H (Fin.last ell) := by
    simpa [hlo0] using hlo
  have hhi' : H (Fin.last ell) ≤ 0 := by
    simpa [hhi0] using hhi
  exact le_antisymm hhi' hlo'

/-- The lower displayed chain has only the two increment values `M-1` and
`M`. -/
theorem aoyagiHtildeLowerChain_F_twoValue (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (j : Fin ell) :
    aoyagiLemma4F ell m (aoyagiHtildeLowerChain ell a M m) j = M - 1 ∨
      aoyagiLemma4F ell m (aoyagiHtildeLowerChain ell a M m) j = M := by
  rw [aoyagiHtildeLowerChain_F_eq]
  by_cases hj : (j : ℕ) < a <;> simp [hj]

/-- The upper displayed chain has only the two increment values `M-1` and
`M`. -/
theorem aoyagiHtildeUpperChain_F_twoValue (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell) (j : Fin ell) :
    aoyagiLemma4F ell m (aoyagiHtildeUpperChain ell a M m) j = M - 1 ∨
      aoyagiLemma4F ell m (aoyagiHtildeUpperChain ell a M m) j = M := by
  rw [aoyagiHtildeUpperChain_F_eq ell a M m ha]
  by_cases hj : (j : ℕ) < ell - a <;> simp [hj]

/-- Lemma 4's two-value count with same-coordinate `Htilde`-chain bounds
replacing an explicit terminal condition.

This still assumes the two-value increment hypothesis for the intermediate
chain. -/
theorem aoyagiLemma4_twoValueCount_of_HtildeChainBounds (ell a : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hlower : aoyagiHtildeLowerChain ell a M m ≤ H)
    (hupper : H ≤ aoyagiHtildeUpperChain ell a M m)
    (hvals : ∀ j : Fin ell,
      aoyagiLemma4F ell m H j = M - 1 ∨ aoyagiLemma4F ell m H j = M) :
    ((Finset.univ.filter fun j : Fin ell ↦ aoyagiLemma4F ell m H j = M).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m H j = M - 1).card = ell - a) := by
  have hHlast :=
    aoyagiLemma4_Hlast_eq_zero_of_HtildeChainBounds ell a M m H ha hselected
      hlower hupper
  exact aoyagiLemma4_twoValueCount_of_terminalH ell a M m H hH0 hHlast hselected hvals

/-- Same-coordinate `Htilde`-chain bound wrapper for the finite
Lemma 4-to-Lemma 3 free-count bridge. -/
theorem aoyagiLemma4_HtildeChainBounds_freeHighCount_lemma3A_eq_min
    (n a : ℕ) (M : ℤ) (m H : Fin (n + 2) → ℤ)
    (hH0 : H 0 = m 0)
    (ha : a ≤ n + 1)
    (hselected : (∑ j : Fin (n + 2), m j) =
      ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hlower : aoyagiHtildeLowerChain (n + 1) a M m ≤ H)
    (hupper : H ≤ aoyagiHtildeUpperChain (n + 1) a M m)
    (hvals : ∀ j : Fin (n + 1),
      aoyagiLemma4F (n + 1) m H j = M - 1 ∨
        aoyagiLemma4F (n + 1) m H j = M) :
    aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
        ((Finset.univ.filter fun j : Fin n ↦
          aoyagiLemma4F (n + 1) m H j.castSucc = M).card : ℤ) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  have hHlast :=
    aoyagiLemma4_Hlast_eq_zero_of_HtildeChainBounds (n + 1) a M m H ha hselected
      hlower hupper
  exact aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min n a M m H hH0
    hHlast hselected hvals

/-- The lower displayed chain satisfies Lemma 4's finite two-value count. -/
theorem aoyagiHtildeLowerChain_twoValueCount (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m (aoyagiHtildeLowerChain ell a M m) j = M).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m (aoyagiHtildeLowerChain ell a M m) j = M - 1).card =
          ell - a) := by
  exact aoyagiLemma4_twoValueCount_of_terminalH ell a M m
    (aoyagiHtildeLowerChain ell a M m)
    (aoyagiHtildeLowerChain_zero ell a M m)
    (aoyagiHtildeLowerChain_last_eq_zero_of_selectedSum ell a M m ha hselected)
    hselected
    (aoyagiHtildeLowerChain_F_twoValue ell a M m)

/-- The upper displayed chain satisfies Lemma 4's finite two-value count. -/
theorem aoyagiHtildeUpperChain_twoValueCount (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m (aoyagiHtildeUpperChain ell a M m) j = M).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m (aoyagiHtildeUpperChain ell a M m) j = M - 1).card =
          ell - a) := by
  exact aoyagiLemma4_twoValueCount_of_terminalH ell a M m
    (aoyagiHtildeUpperChain ell a M m)
    (aoyagiHtildeUpperChain_zero ell a M m)
    (aoyagiHtildeUpperChain_last_eq_zero_of_selectedSum ell a M m ha hselected)
    hselected
    (aoyagiHtildeUpperChain_F_twoValue ell a M m ha)

end Aoyagi
end DLN
end DLNFibre
