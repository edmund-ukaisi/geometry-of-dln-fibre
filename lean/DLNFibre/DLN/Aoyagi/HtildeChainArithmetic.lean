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

/-- Source-selected widths are bounded above by `M-1`.

This is the finite arithmetic content of Definition 3's strict selected
inequality: for every selected width `W_i`, the selected sum is strictly
larger than `ell*W_i`.  Together with
`sum W = ell*(M-1)+a` and `a<=ell`, this forces `W_i < M`, hence
`W_i <= M-1`. -/
theorem aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (i : Fin (ell + 1)) :
    m i ≤ M - 1 := by
  by_contra hnot
  have hMi : M ≤ m i := by omega
  have hell_pos : (0 : ℤ) < (ell : ℤ) := by exact_mod_cast hell
  have ha_int : (a : ℤ) ≤ (ell : ℤ) := by exact_mod_cast ha
  have hstrict := hsource i
  rw [hselected] at hstrict
  nlinarith

/-- If every selected width is at most `M-1`, then the previous selected-width
prefix before coordinate `p` is at most `p*M-1`.

This is the upper half of the equation `(4)` label-bound calculation. -/
theorem aoyagiPrefixSum_sub_current_add_one_le_mul_of_selectedWidth_le_pred
    (ell p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hp0 : 1 ≤ p) (hpell : p ≤ ell)
    (hbound : ∀ i : Fin (ell + 1), m i ≤ M - 1) :
    aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) p -
        aoyagiSelectedWidthNat ell m p + 1 ≤
      (p : ℤ) * M := by
  have hprefix :
      aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) p -
          aoyagiSelectedWidthNat ell m p =
        ∑ i ∈ Finset.range p, aoyagiSelectedWidthNat ell m i := by
    unfold aoyagiPrefixSum
    rw [Finset.sum_range_succ]
    ring
  have hterm :
      ∀ i ∈ Finset.range p, aoyagiSelectedWidthNat ell m i ≤ M - 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_lt : i < ell + 1 := by omega
    rw [aoyagiSelectedWidthNat_of_lt hi_lt]
    exact hbound ⟨i, hi_lt⟩
  have hsum_le :
      (∑ i ∈ Finset.range p, aoyagiSelectedWidthNat ell m i) ≤
        (∑ _i ∈ Finset.range p, (M - 1 : ℤ)) := by
    exact Finset.sum_le_sum hterm
  have hsum_const :
      (∑ _i ∈ Finset.range p, (M - 1 : ℤ)) = (p : ℤ) * (M - 1) := by
    simp
    ring
  have hprev_le :
      (∑ i ∈ Finset.range p, aoyagiSelectedWidthNat ell m i) ≤
        (p : ℤ) * (M - 1) := by
    rw [hsum_const] at hsum_le
    exact hsum_le
  have hslack : (p : ℤ) * (M - 1) + 1 ≤ (p : ℤ) * M := by
    have hp0_int : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp0
    nlinarith
  rw [hprefix]
  linarith

/-- If every selected width is at most `M-1`, then the selected-width prefix
through coordinate `p` is at least `p*M`.

The proof uses the tail after `p`: under the selected-sum identity, the tail
has `ell-p` terms and each is at most `M-1`, so the prefix is at least
`p*(M-1)+a`, hence at least `p*M` when `p<=a`. -/
theorem aoyagiPrefixSum_mul_le_of_selectedWidth_le_pred
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hp_a : p ≤ a) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hbound : ∀ i : Fin (ell + 1), m i ≤ M - 1) :
    (p : ℤ) * M ≤ aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) p := by
  let w := aoyagiSelectedWidthNat ell m
  let P := aoyagiPrefixSum w
  let tail := ∑ i ∈ Finset.Ico (p + 1) (ell + 1), w i
  have hpell : p ≤ ell := le_trans hp_a ha
  have hsplit : P p + tail = P ell := by
    dsimp [P, tail, aoyagiPrefixSum]
    exact Finset.sum_range_add_sum_Ico w (by omega)
  have htotal : P p + tail = (ell : ℤ) * (M - 1) + a := by
    rw [hsplit]
    dsimp [P, w]
    rw [aoyagiPrefixSum_selectedWidthNat_last, hselected]
  have htail_terms :
      ∀ i ∈ Finset.Ico (p + 1) (ell + 1), w i ≤ M - 1 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    dsimp [w]
    rw [aoyagiSelectedWidthNat_of_lt hi.2]
    exact hbound ⟨i, hi.2⟩
  have htail_le_sum :
      tail ≤ ∑ _i ∈ Finset.Ico (p + 1) (ell + 1), (M - 1 : ℤ) := by
    exact Finset.sum_le_sum htail_terms
  have htail_const :
      (∑ _i ∈ Finset.Ico (p + 1) (ell + 1), (M - 1 : ℤ)) =
        ((ell - p : ℕ) : ℤ) * (M - 1) := by
    have hcard : (Finset.Ico (p + 1) (ell + 1)).card = ell - p := by
      rw [Nat.card_Ico]
      omega
    simp [hcard]
    ring
  have htail_le :
      tail ≤ ((ell - p : ℕ) : ℤ) * (M - 1) := by
    rw [htail_const] at htail_le_sum
    exact htail_le_sum
  have hprefix_from_tail :
      (ell : ℤ) * (M - 1) + (a : ℤ) -
          ((ell - p : ℕ) : ℤ) * (M - 1) ≤ P p := by
    linarith
  have hprefix_floor :
      (ell : ℤ) * (M - 1) + (a : ℤ) -
          ((ell - p : ℕ) : ℤ) * (M - 1) =
        (p : ℤ) * (M - 1) + (a : ℤ) := by
    rw [Nat.cast_sub hpell]
    ring
  have hp_le_a_int : (p : ℤ) ≤ (a : ℤ) := by exact_mod_cast hp_a
  have hpM_le_floor : (p : ℤ) * M ≤ (p : ℤ) * (M - 1) + (a : ℤ) := by
    nlinarith
  rw [hprefix_floor] at hprefix_from_tail
  exact le_trans hpM_le_floor hprefix_from_tail

/-- Source-shaped form: Definition 3's strict selected-width inequalities
prove the lower half of equation `(4)`'s prefix-crossing condition. -/
theorem aoyagiPrefixSum_mul_le_of_sourceSelectedInequality
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp_a : p ≤ a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    (p : ℤ) * M ≤ aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) p := by
  have hbound : ∀ i : Fin (ell + 1), m i ≤ M - 1 :=
    aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
      ell a M m hell ha hselected hsource
  exact aoyagiPrefixSum_mul_le_of_selectedWidth_le_pred
    ell a p M m hp_a ha hselected hbound

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

/-- Nat-indexed form of the lower displayed chain's terminal zero. -/
theorem aoyagiHtildeLowerNat_last_eq_zero_of_selectedSum (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    aoyagiHtildeLowerNat ell a M m ell = 0 := by
  simpa [aoyagiHtildeLowerChain] using
    aoyagiHtildeLowerChain_last_eq_zero_of_selectedSum ell a M m ha hselected

/-- Nat-indexed form of the upper displayed chain's terminal zero. -/
theorem aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    aoyagiHtildeUpperNat ell a M m ell = 0 := by
  simpa [aoyagiHtildeUpperChain] using
    aoyagiHtildeUpperChain_last_eq_zero_of_selectedSum ell a M m ha hselected

/-- Under the selected-width sum, the penultimate upper-chain value is
`M-W_(ell+1)`.

This is only endpoint arithmetic for the displayed upper `Htilde'` chain. -/
theorem aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha_pos : 1 ≤ a) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    aoyagiHtildeUpperNat ell a M m (ell - 1) =
      M - aoyagiSelectedWidthNat ell m ell := by
  let w := aoyagiSelectedWidthNat ell m
  let P := aoyagiPrefixSum w
  have hell_pos : 1 ≤ ell := le_trans ha_pos ha
  have hpred_succ : ell - 1 + 1 = ell := by omega
  have hprefix_succ := aoyagiPrefixSum_succ w (ell - 1)
  have hprefix :
      P (ell - 1) = P ell - w ell := by
    dsimp [P]
    rw [hpred_succ] at hprefix_succ
    linarith
  have htotal : P ell = (ell : ℤ) * (M - 1) + a := by
    dsimp [P, w]
    rw [aoyagiPrefixSum_selectedWidthNat_last, hselected]
  have hsub : (ell - 1) - (ell - a) = a - 1 := by omega
  have hmin : min a ((ell - 1) - (ell - a)) = a - 1 := by
    rw [hsub]
    exact Nat.min_eq_right (by omega)
  unfold aoyagiHtildeUpperNat aoyagiHtildeUpperIncrementPrefix
    aoyagiHtildeUpperHighCount
  change aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) (ell - 1) -
      (((ell - 1 : ℕ) : ℤ) * (M - 1) +
        (((min a ((ell - 1) - (ell - a))) : ℕ) : ℤ)) =
    M - aoyagiSelectedWidthNat ell m ell
  change P (ell - 1) -
      (((ell - 1 : ℕ) : ℤ) * (M - 1) +
        (((min a ((ell - 1) - (ell - a))) : ℕ) : ℤ)) =
    M - w ell
  rw [hprefix, htotal, hmin]
  have hell_pred_cast : ((ell - 1 : ℕ) : ℤ) = (ell : ℤ) - 1 := by
    exact_mod_cast (Nat.sub_eq_iff_eq_add hell_pos).2 hpred_succ.symm
  have ha_pred_cast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
    exact_mod_cast (Nat.sub_eq_iff_eq_add ha_pos).2 (by omega)
  rw [hell_pred_cast, ha_pred_cast]
  ring

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

/-- In the rising part of Aoyagi's displayed interval, the upper chain minus
the coordinate index is the lower chain.

For Lemma 5 equation `(4)`, this is the finite arithmetic behind the extra
guard `j0 <= ell-a`: the printed own-coordinate value `Htilde'_j0 - j0`
equals `Htilde_j0`.  It does not assert that the displayed source vector is
legal, terminal, or admissible. -/
theorem aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (j : Fin (ell + 1))
    (hj_a : j.val ≤ a) (hj_c : j.val ≤ ell - a) :
    aoyagiHtildeUpperChain ell a M m j - (j.val : ℤ) =
      aoyagiHtildeLowerChain ell a M m j := by
  have hgap := aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m ha j
  have hexcess : aoyagiLemma5IntervalExcess ell a j.val = j.val := by
    exact aoyagiLemma5IntervalExcess_eq_self_of_le_min ell a j.val ha hj_a hj_c
  rw [hexcess] at hgap
  omega

/-- Nat-indexed form of
`aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min`. -/
theorem aoyagiHtildeUpperNat_sub_index_eq_lowerNat_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    aoyagiHtildeUpperNat ell a M m p - (p : ℤ) =
      aoyagiHtildeLowerNat ell a M m p := by
  have hp_lt : p < ell + 1 := by omega
  simpa [aoyagiHtildeUpperChain, aoyagiHtildeLowerChain] using
    aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min
      ell a M m ha ⟨p, hp_lt⟩ hp_a hp_c

/-- Equation `(4)` lower-label bounds are exactly a prefix-crossing condition.

For the source label `k = Htilde_p+1`, the lower and upper label inequalities
`1 <= k <= W_(p+1)` are equivalent to saying that the threshold `p*M` lies
between the previous selected-width prefix and the current selected-width
prefix.  This is a conditional arithmetic reformulation only; it does not
prove that Aoyagi's displayed vector is a legal source-family member. -/
theorem aoyagiHtildeLowerNat_add_one_labelBounds_iff_prefixCrossing
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hp_a : p ≤ a) :
    (1 ≤ aoyagiHtildeLowerNat ell a M m p + 1 ∧
        aoyagiHtildeLowerNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p) ↔
      (aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) p -
          aoyagiSelectedWidthNat ell m p + 1 ≤ (p : ℤ) * M ∧
        (p : ℤ) * M ≤
          aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) p) := by
  unfold aoyagiHtildeLowerNat aoyagiHtildeLowerIncrementPrefix
    aoyagiHtildeLowerHighCount
  rw [Nat.min_eq_left hp_a]
  have hprefix :
      (p : ℤ) * (M - 1) + (p : ℤ) = (p : ℤ) * M := by
    ring
  rw [hprefix]
  constructor
  · intro h
    constructor <;> omega
  · intro h
    constructor <;> omega

/-- The selected-width upper bound proves the upper half of equation `(4)`'s
label bound. -/
theorem aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_selectedWidth_le_pred
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hp0 : 1 ≤ p) (hp_a : p ≤ a) (hpell : p ≤ ell)
    (hbound : ∀ i : Fin (ell + 1), m i ≤ M - 1) :
    aoyagiHtildeLowerNat ell a M m p + 1 ≤
      aoyagiSelectedWidthNat ell m p := by
  have hprefix :=
    aoyagiPrefixSum_sub_current_add_one_le_mul_of_selectedWidth_le_pred
      ell p M m hp0 hpell hbound
  unfold aoyagiHtildeLowerNat aoyagiHtildeLowerIncrementPrefix
    aoyagiHtildeLowerHighCount
  rw [Nat.min_eq_left hp_a]
  have hprefixM :
      (p : ℤ) * (M - 1) + (p : ℤ) = (p : ℤ) * M := by
    ring
  rw [hprefixM]
  omega

/-- Source-shaped form: Definition 3's strict selected-width inequalities
prove the upper half of equation `(4)`'s label bound.

The companion lower-bound theorem below proves the other label inequality from
the same source hypotheses.  Neither theorem constructs the displayed vector,
terminal `tilde t=0`, or the chart family. -/
theorem aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_sourceSelectedInequality
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp0 : 1 ≤ p) (hp_a : p ≤ a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    aoyagiHtildeLowerNat ell a M m p + 1 ≤
      aoyagiSelectedWidthNat ell m p := by
  have hbound : ∀ i : Fin (ell + 1), m i ≤ M - 1 :=
    aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
      ell a M m hell ha hselected hsource
  exact aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_selectedWidth_le_pred
    ell a p M m hp0 hp_a (le_trans hp_a ha) hbound

/-- The selected-width upper bound and selected-sum identity prove the lower
half of equation `(4)`'s label bound. -/
theorem aoyagiHtildeLowerNat_add_one_pos_of_selectedWidth_le_pred
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hp_a : p ≤ a) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hbound : ∀ i : Fin (ell + 1), m i ≤ M - 1) :
    1 ≤ aoyagiHtildeLowerNat ell a M m p + 1 := by
  have hprefix := aoyagiPrefixSum_mul_le_of_selectedWidth_le_pred
    ell a p M m hp_a ha hselected hbound
  unfold aoyagiHtildeLowerNat aoyagiHtildeLowerIncrementPrefix
    aoyagiHtildeLowerHighCount
  rw [Nat.min_eq_left hp_a]
  have hprefixM :
      (p : ℤ) * (M - 1) + (p : ℤ) = (p : ℤ) * M := by
    ring
  rw [hprefixM]
  omega

/-- Source-shaped form: Definition 3's strict selected-width inequalities
prove the lower half of equation `(4)`'s label bound. -/
theorem aoyagiHtildeLowerNat_add_one_pos_of_sourceSelectedInequality
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp_a : p ≤ a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    1 ≤ aoyagiHtildeLowerNat ell a M m p + 1 := by
  have hbound : ∀ i : Fin (ell + 1), m i ≤ M - 1 :=
    aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
      ell a M m hell ha hselected hsource
  exact aoyagiHtildeLowerNat_add_one_pos_of_selectedWidth_le_pred
    ell a p M m hp_a ha hselected hbound

/-- Definition 3's selected-width arithmetic proves both label bounds for
Aoyagi Lemma 5 equation `(4)`'s `k=Htilde_p+1`.

This is still only label arithmetic.  It does not prove the displayed source
vector, terminal `tilde t=0`, vector admissibility, chart coverage, pole
order, normal crossings, or RLCT extraction. -/
theorem aoyagiHtildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp0 : 1 ≤ p) (hp_a : p ≤ a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    1 ≤ aoyagiHtildeLowerNat ell a M m p + 1 ∧
      aoyagiHtildeLowerNat ell a M m p + 1 ≤
        aoyagiSelectedWidthNat ell m p := by
  constructor
  · exact aoyagiHtildeLowerNat_add_one_pos_of_sourceSelectedInequality
      ell a p M m hell ha hp_a hselected hsource
  · exact aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_sourceSelectedInequality
      ell a p M m hell ha hp0 hp_a hselected hsource

/-- Corrected local arithmetic data for Aoyagi Lemma 5 equation `(4)`.

Under the selected-index guard `p+1<=a` and the own-coordinate guard
`p<=ell-a`, the displayed tail cutoff is in the selected list, the
own-coordinate value is `Htilde_p`, and the source label
`k=Htilde_p+1` is legal.

This is only the local equation `(4)` arithmetic package.  It does not
construct the displayed source vector, prove terminal `tilde t=0`, prove
vector admissibility, or prove the Lemma 5 chart-family/order count. -/
theorem aoyagiLemma5Eq4_localData_of_sourceSelectedInequality
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp0 : 1 ≤ p)
    (hp_tail : p + 1 ≤ a) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    p + (ell - a) + 2 ≤ ell + 1 ∧
      aoyagiHtildeUpperNat ell a M m p - (p : ℤ) =
        aoyagiHtildeLowerNat ell a M m p ∧
      (1 ≤ aoyagiHtildeLowerNat ell a M m p + 1 ∧
        aoyagiHtildeLowerNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p) := by
  have hp_a : p ≤ a := by omega
  constructor
  · exact (aoyagiLemma5Eq4_selectedIndexGuard_iff ell a p ha).2 hp_tail
  constructor
  · exact aoyagiHtildeUpperNat_sub_index_eq_lowerNat_of_le_min
      ell a p M m ha hp_a hp_c
  · exact aoyagiHtildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
      ell a p M m hell ha hp0 hp_a hselected hsource

/-- In the interior case of equation `(3)`, the first upper/lower Htilde gap
is exactly one.

This is the arithmetic behind the fact that the source's exceptional label
`k=Htilde'_1+1` is one step above the lower endpoint.  It does not prove that
the label is legal or terminal. -/
theorem aoyagiHtildeUpperNat_one_sub_lowerNat_one_of_pos_of_lt
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha_pos : 1 ≤ a) (ha_lt : a < ell) :
    aoyagiHtildeUpperNat ell a M m 1 -
        aoyagiHtildeLowerNat ell a M m 1 =
      1 := by
  have ha : a ≤ ell := by omega
  have h1_lt : 1 < ell + 1 := by omega
  have hgap :=
    aoyagiHtildeUpper_sub_lower_eq_intervalExcess
      ell a M m ha ⟨1, h1_lt⟩
  have hexcess : aoyagiLemma5IntervalExcess ell a 1 = 1 := by
    exact aoyagiLemma5IntervalExcess_eq_self_of_le_min
      ell a 1 ha ha_pos (by omega)
  simpa [aoyagiHtildeUpperChain, aoyagiHtildeLowerChain, hexcess] using hgap

/-- Equation `(3)` first-upper label bounds are exactly two explicit selected
width inequalities when the first upper arm is active.

When `a<ell`, `Htilde'_1 = W_1+W_2-(M-1)`, so the bounds for
`k=Htilde'_1+1` are equivalent to `M-1 <= W_1+W_2` and `W_1+2 <= M`.
This is only a finite arithmetic reformulation, not a proof that Aoyagi's
displayed exceptional label is source-legal. -/
theorem aoyagiHtildeUpperNat_one_add_one_labelBounds_iff_widthGuards
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha_lt : a < ell) :
    (1 ≤ aoyagiHtildeUpperNat ell a M m 1 + 1 ∧
        aoyagiHtildeUpperNat ell a M m 1 + 1 ≤
          aoyagiSelectedWidthNat ell m 1) ↔
      (M - 1 ≤ aoyagiSelectedWidthNat ell m 0 +
          aoyagiSelectedWidthNat ell m 1 ∧
        aoyagiSelectedWidthNat ell m 0 + 2 ≤ M) := by
  have hupper :
      aoyagiHtildeUpperNat ell a M m 1 =
        aoyagiSelectedWidthNat ell m 0 +
            aoyagiSelectedWidthNat ell m 1 - (M - 1) := by
    unfold aoyagiHtildeUpperNat aoyagiHtildeUpperIncrementPrefix
      aoyagiHtildeUpperHighCount
    have hprefix :
        aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) 1 =
          aoyagiSelectedWidthNat ell m 0 + aoyagiSelectedWidthNat ell m 1 := by
      simpa using aoyagiPrefixSum_succ (aoyagiSelectedWidthNat ell m) 0
    have hsub : 1 - (ell - a) = 0 := by omega
    rw [hsub, hprefix]
    simp
  rw [hupper]
  constructor
  · intro h
    constructor <;> omega
  · intro h
    constructor <;> omega

/-- Corrected local arithmetic data for Aoyagi Lemma 5 equation `(3)`.

Under the selected-index guard `1<=a`, the interior guard `a<ell`, and the
explicit one-unit width guards, the displayed special cutoff is in the
selected list, the first upper/lower gap is one, and the source label
`k=Htilde'_1+1` is legal.

This is only the local equation `(3)` arithmetic package.  It does not
construct the displayed source vector, prove terminal `tilde t=0`, prove
vector admissibility, or prove the Lemma 5 chart-family/order count. -/
theorem aoyagiLemma5Eq3_localData_of_widthGuards
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha_pos : 1 ≤ a) (ha_lt : a < ell)
    (hwidth :
      M - 1 ≤ aoyagiSelectedWidthNat ell m 0 +
          aoyagiSelectedWidthNat ell m 1 ∧
        aoyagiSelectedWidthNat ell m 0 + 2 ≤ M) :
    (ell - a) + 2 ≤ ell + 1 ∧
      aoyagiHtildeUpperNat ell a M m 1 -
          aoyagiHtildeLowerNat ell a M m 1 =
        1 ∧
      (1 ≤ aoyagiHtildeUpperNat ell a M m 1 + 1 ∧
        aoyagiHtildeUpperNat ell a M m 1 + 1 ≤
          aoyagiSelectedWidthNat ell m 1) := by
  have ha : a ≤ ell := by omega
  constructor
  · exact (aoyagiLemma5Eq3_selectedIndexGuard_iff ell a ha).2 ha_pos
  constructor
  · exact aoyagiHtildeUpperNat_one_sub_lowerNat_one_of_pos_of_lt
      ell a M m ha_pos ha_lt
  · exact
      (aoyagiHtildeUpperNat_one_add_one_labelBounds_iff_widthGuards
        ell a M m ha_lt).2 hwidth

/-- Definition 3's selected-width inequalities prove equation `(3)`'s first
label guard; the remaining one-unit slack is kept explicit.

The counterexamples with `W_1=W_2=M-1` show that the slack
`W_1+2<=M` is not a consequence of Definition 3 alone. -/
theorem aoyagiHtildeUpperNat_one_add_one_labelBounds_of_sourceSelectedInequality_and_slack
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (ha_pos : 1 ≤ a) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M) :
    1 ≤ aoyagiHtildeUpperNat ell a M m 1 + 1 ∧
      aoyagiHtildeUpperNat ell a M m 1 + 1 ≤
        aoyagiSelectedWidthNat ell m 1 := by
  have hprefix :
      aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) 1 =
        aoyagiSelectedWidthNat ell m 0 + aoyagiSelectedWidthNat ell m 1 := by
    simpa using aoyagiPrefixSum_succ (aoyagiSelectedWidthNat ell m) 0
  have hM_le_prefix :
      M ≤ aoyagiSelectedWidthNat ell m 0 +
          aoyagiSelectedWidthNat ell m 1 := by
    have h :=
      aoyagiPrefixSum_mul_le_of_sourceSelectedInequality
        ell a 1 M m hell ha ha_pos hselected hsource
    rw [hprefix] at h
    simpa using h
  have hwidth :
      M - 1 ≤ aoyagiSelectedWidthNat ell m 0 +
          aoyagiSelectedWidthNat ell m 1 ∧
        aoyagiSelectedWidthNat ell m 0 + 2 ≤ M := by
    constructor
    · linarith
    · exact hslack
  exact
    (aoyagiHtildeUpperNat_one_add_one_labelBounds_iff_widthGuards
      ell a M m ha_lt).2 hwidth

/-- Source-shaped equation `(3)` local data: Definition 3 supplies the first
label guard, while the missing one-unit slack is explicit. -/
theorem aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (ha_pos : 1 ≤ a) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M) :
    (ell - a) + 2 ≤ ell + 1 ∧
      aoyagiHtildeUpperNat ell a M m 1 -
      aoyagiHtildeLowerNat ell a M m 1 =
        1 ∧
      (1 ≤ aoyagiHtildeUpperNat ell a M m 1 + 1 ∧
        aoyagiHtildeUpperNat ell a M m 1 + 1 ≤
          aoyagiSelectedWidthNat ell m 1) := by
  exact aoyagiLemma5Eq3_localData_of_widthGuards ell a M m ha_pos ha_lt
    ⟨by
      have hprefix :
          aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) 1 =
            aoyagiSelectedWidthNat ell m 0 + aoyagiSelectedWidthNat ell m 1 := by
        simpa using aoyagiPrefixSum_succ (aoyagiSelectedWidthNat ell m) 0
      have h :=
        aoyagiPrefixSum_mul_le_of_sourceSelectedInequality
          ell a 1 M m hell ha ha_pos hselected hsource
      rw [hprefix] at h
      have hM_le :
          M ≤ aoyagiSelectedWidthNat ell m 0 +
              aoyagiSelectedWidthNat ell m 1 := by
        simpa using h
      linarith,
    hslack⟩

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

/-- Nat-indexed same-coordinate value set between the two displayed chains.

The wrapper is empty outside the source coordinate range.  This lets source
statements sum over ordinary natural-number intervals while keeping the
range guard explicit in cardinality lemmas. -/
def aoyagiHtildeIntervalValueSetNat (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (j : ℕ) : Finset ℤ :=
  if h : j < ell + 1 then
    aoyagiHtildeIntervalValueSet ell a M m ⟨j, h⟩
  else
    ∅

/-- In range, the Nat-indexed same-coordinate value set has Aoyagi's displayed
interval size. -/
theorem aoyagiHtildeIntervalValueSetNat_card_of_lt
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) (j : ℕ)
    (hj : j < ell + 1) :
    (aoyagiHtildeIntervalValueSetNat ell a M m j).card =
      aoyagiLemma5IntervalSize ell a j := by
  simp [aoyagiHtildeIntervalValueSetNat, hj,
    aoyagiHtildeIntervalValueSet_card]

/-- Cardinality of the Nat-indexed same-coordinate value set, with the
out-of-range case made explicit. -/
theorem aoyagiHtildeIntervalValueSetNat_card
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) (j : ℕ) :
    (aoyagiHtildeIntervalValueSetNat ell a M m j).card =
      if j < ell + 1 then aoyagiLemma5IntervalSize ell a j else 0 := by
  by_cases hj : j < ell + 1
  · simp [aoyagiHtildeIntervalValueSetNat, hj,
      aoyagiHtildeIntervalValueSet_card]
  · simp [aoyagiHtildeIntervalValueSetNat, hj]

/-- Source-facing finite value-set count behind Aoyagi's Lemma 5 interval
arithmetic.

This counts only the same-coordinate `H`-values between the two displayed
`Htilde` chains.  It is not the chart-family admissibility, coverage, pole
order, normal-crossing, or RLCT statement of Lemma 5. -/
theorem aoyagiHtildeIntervalValueSetNat_excess_sum_Icc
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) :
    1 + (∑ j ∈ Finset.Icc 1 (ell - 1),
        ((aoyagiHtildeIntervalValueSetNat ell a M m j).card - 1)) =
      a * (ell - a) + 1 := by
  rw [← aoyagiLemma5IntervalSize_excess_sum_Icc ell a hell ha]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < ell + 1 := by
    have hjle : j ≤ ell - 1 := (Finset.mem_Icc.mp hj).2
    omega
  rw [aoyagiHtildeIntervalValueSetNat_card_of_lt ell a M m j hjlt]

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

/-- Prefix-delta normal form for an arbitrary `H` chain.

This is a finite bookkeeping device for the two-value increment blocker.  It
does not assert that the prefix deltas are binary for source exponent vectors. -/
def aoyagiLemma4IncrementPrefix (ell : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ) (j : Fin (ell + 1)) : ℤ :=
  aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) j.val -
    H j - (j.val : ℤ) * (M - 1)

/-- Successive change in the Lemma 4 prefix-delta normal form. -/
def aoyagiLemma4IncrementPrefixDelta (ell : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ) (j : Fin ell) : ℤ :=
  aoyagiLemma4IncrementPrefix ell M m H j.succ -
    aoyagiLemma4IncrementPrefix ell M m H j.castSucc

/-- The increment `F_j` is `M-1` plus the successive prefix-delta change. -/
theorem aoyagiLemma4F_eq_pred_add_incrementPrefixDelta
    (ell : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ) (j : Fin ell) :
    aoyagiLemma4F ell m H j =
      (M - 1) +
        (aoyagiLemma4IncrementPrefix ell M m H j.succ -
          aoyagiLemma4IncrementPrefix ell M m H j.castSucc) := by
  unfold aoyagiLemma4F aoyagiLemma4IncrementPrefix
  have hprefix :
      aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) (j.val + 1) =
        aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) j.val + m j.succ := by
    rw [aoyagiPrefixSum_succ]
    rw [aoyagiSelectedWidthNat_succ_fin m j]
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [hprefix]
  have hcast : ((j.val + 1 : ℕ) : ℤ) = (j.val : ℤ) + 1 := by
    norm_num
  rw [hcast]
  ring_nf

/-- Definitional wrapper for the prefix-delta version of the increment
identity. -/
theorem aoyagiLemma4F_eq_pred_add_incrementPrefixDelta_def
    (ell : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ) (j : Fin ell) :
    aoyagiLemma4F ell m H j =
      (M - 1) + aoyagiLemma4IncrementPrefixDelta ell M m H j := by
  rw [aoyagiLemma4F_eq_pred_add_incrementPrefixDelta]
  rfl

/-- Binary named prefix deltas imply the two-value increment hypothesis in
Aoyagi's Lemma 4.

This is the `aoyagiLemma4IncrementPrefixDelta`-named form of the binary bridge.
It remains conditional: no source vector, chain bound, or admissibility
statement is proved here. -/
theorem aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta
    (ell : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hbin : ∀ j : Fin ell,
      aoyagiLemma4IncrementPrefixDelta ell M m H j = 0 ∨
        aoyagiLemma4IncrementPrefixDelta ell M m H j = 1) :
    ∀ j : Fin ell,
      aoyagiLemma4F ell m H j = M - 1 ∨
        aoyagiLemma4F ell m H j = M := by
  intro j
  rw [aoyagiLemma4F_eq_pred_add_incrementPrefixDelta_def ell M m H j]
  rcases hbin j with hzero | hone
  · left
    omega
  · right
    omega

/-- Binary prefix deltas imply the two-value increment hypothesis in
Aoyagi's Lemma 4.

This is only a conditional finite bridge.  It does not prove that source vector
bounds or exponent admissibility provide the binary prefix-delta hypothesis. -/
theorem aoyagiLemma4F_twoValue_of_binaryIncrementPrefix
    (ell : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hbin : ∀ j : Fin ell,
      aoyagiLemma4IncrementPrefix ell M m H j.succ -
          aoyagiLemma4IncrementPrefix ell M m H j.castSucc = 0 ∨
        aoyagiLemma4IncrementPrefix ell M m H j.succ -
          aoyagiLemma4IncrementPrefix ell M m H j.castSucc = 1) :
    ∀ j : Fin ell,
      aoyagiLemma4F ell m H j = M - 1 ∨
        aoyagiLemma4F ell m H j = M := by
  intro j
  rw [aoyagiLemma4F_eq_pred_add_incrementPrefixDelta ell M m H j]
  rcases hbin j with hzero | hone
  · left
    omega
  · right
    omega

/-- Lemma 4's finite count with the two-value hypothesis supplied by binary
prefix deltas. -/
theorem aoyagiLemma4_twoValueCount_of_terminalH_binaryIncrementPrefix
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0) (hHlast : H (Fin.last ell) = 0)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hbin : ∀ j : Fin ell,
      aoyagiLemma4IncrementPrefix ell M m H j.succ -
          aoyagiLemma4IncrementPrefix ell M m H j.castSucc = 0 ∨
        aoyagiLemma4IncrementPrefix ell M m H j.succ -
          aoyagiLemma4IncrementPrefix ell M m H j.castSucc = 1) :
    ((Finset.univ.filter fun j : Fin ell ↦ aoyagiLemma4F ell m H j = M).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m H j = M - 1).card = ell - a) := by
  exact aoyagiLemma4_twoValueCount_of_terminalH ell a M m H hH0 hHlast hselected
    (aoyagiLemma4F_twoValue_of_binaryIncrementPrefix ell M m H hbin)

/-- Same-coordinate `Htilde`-chain-bound count wrapper with the two-value
hypothesis supplied by binary prefix deltas. -/
theorem aoyagiLemma4_twoValueCount_of_HtildeChainBounds_binaryIncrementPrefix
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hlower : aoyagiHtildeLowerChain ell a M m ≤ H)
    (hupper : H ≤ aoyagiHtildeUpperChain ell a M m)
    (hbin : ∀ j : Fin ell,
      aoyagiLemma4IncrementPrefix ell M m H j.succ -
          aoyagiLemma4IncrementPrefix ell M m H j.castSucc = 0 ∨
        aoyagiLemma4IncrementPrefix ell M m H j.succ -
          aoyagiLemma4IncrementPrefix ell M m H j.castSucc = 1) :
    ((Finset.univ.filter fun j : Fin ell ↦ aoyagiLemma4F ell m H j = M).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m H j = M - 1).card = ell - a) := by
  exact aoyagiLemma4_twoValueCount_of_HtildeChainBounds ell a M m H hH0 ha
    hselected hlower hupper
    (aoyagiLemma4F_twoValue_of_binaryIncrementPrefix ell M m H hbin)

/-- With the source convention `H_0=m_0`, the first prefix delta is zero. -/
theorem aoyagiLemma4IncrementPrefix_zero_of_H0
    (ell : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0) :
    aoyagiLemma4IncrementPrefix ell M m H 0 = 0 := by
  simp [aoyagiLemma4IncrementPrefix, hH0]

/-- With terminal `H_ell=0` and the selected-width sum, the last prefix
delta is `a`. -/
theorem aoyagiLemma4IncrementPrefix_last_eq_a_of_terminalH
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hHlast : H (Fin.last ell) = 0)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    aoyagiLemma4IncrementPrefix ell M m H (Fin.last ell) = a := by
  unfold aoyagiLemma4IncrementPrefix
  simp only [Fin.val_last]
  rw [aoyagiPrefixSum_selectedWidthNat_last ell m, hselected, hHlast]
  ring

/-- The sum of successive prefix deltas telescopes to the endpoint
difference. -/
theorem aoyagiLemma4IncrementPrefixDelta_sum_eq_last_sub_zero
    (ell : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ) :
    (∑ j : Fin ell, aoyagiLemma4IncrementPrefixDelta ell M m H j) =
      aoyagiLemma4IncrementPrefix ell M m H (Fin.last ell) -
        aoyagiLemma4IncrementPrefix ell M m H 0 := by
  let D : Fin (ell + 1) → ℤ := fun j ↦ aoyagiLemma4IncrementPrefix ell M m H j
  change (∑ j : Fin ell, (D j.succ - D j.castSucc)) =
    D (Fin.last ell) - D 0
  rw [Finset.sum_sub_distrib]
  have hsucc :
      (∑ j : Fin ell, D j.succ) =
        (∑ j : Fin (ell + 1), D j) - D 0 := by
    have h := Fin.sum_univ_succ D
    omega
  have hcast :
      (∑ j : Fin ell, D j.castSucc) =
        (∑ j : Fin (ell + 1), D j) - D (Fin.last ell) := by
    have h := Fin.sum_univ_castSucc D
    omega
  rw [hsucc, hcast]
  omega

/-- Under the terminal source hypotheses, the sum of prefix deltas is `a`. -/
theorem aoyagiLemma4IncrementPrefixDelta_sum_eq_a_of_terminalH
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0) (hHlast : H (Fin.last ell) = 0)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    (∑ j : Fin ell, aoyagiLemma4IncrementPrefixDelta ell M m H j) = a := by
  rw [aoyagiLemma4IncrementPrefixDelta_sum_eq_last_sub_zero]
  rw [aoyagiLemma4IncrementPrefix_zero_of_H0 ell M m H hH0]
  rw [aoyagiLemma4IncrementPrefix_last_eq_a_of_terminalH ell a M m H hHlast hselected]
  omega

/-- Binary prefix deltas are counted by the endpoint excess `a` under the
terminal source hypotheses. -/
theorem aoyagiLemma4_binaryIncrementPrefix_count_eq
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0) (hHlast : H (Fin.last ell) = 0)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hbin : ∀ j : Fin ell,
      aoyagiLemma4IncrementPrefixDelta ell M m H j = 0 ∨
        aoyagiLemma4IncrementPrefixDelta ell M m H j = 1) :
    ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4IncrementPrefixDelta ell M m H j = 1).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4IncrementPrefixDelta ell M m H j = 0).card = ell - a) := by
  let δ : Fin ell → ℤ := fun j ↦ aoyagiLemma4IncrementPrefixDelta ell M m H j
  have hvals : ∀ j, δ j = 0 ∨ δ j = 0 + 1 := by
    intro j
    rcases hbin j with hzero | hone
    · exact Or.inl hzero
    · right
      simpa using hone
  have hsum : (∑ j : Fin ell, δ j) = (ell : ℤ) * 0 + a := by
    dsimp [δ]
    rw [aoyagiLemma4IncrementPrefixDelta_sum_eq_a_of_terminalH ell a M m H
      hH0 hHlast hselected]
    omega
  have h := twoStepInt_count_eq ell a 0 δ hvals hsum
  simpa [δ] using h

/-- Same-coordinate `Htilde`-chain-bound version of the binary prefix-delta
count.  The binary-delta hypothesis remains explicit. -/
theorem aoyagiLemma4_binaryIncrementPrefix_count_eq_of_HtildeChainBounds
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hlower : aoyagiHtildeLowerChain ell a M m ≤ H)
    (hupper : H ≤ aoyagiHtildeUpperChain ell a M m)
    (hbin : ∀ j : Fin ell,
      aoyagiLemma4IncrementPrefixDelta ell M m H j = 0 ∨
        aoyagiLemma4IncrementPrefixDelta ell M m H j = 1) :
    ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4IncrementPrefixDelta ell M m H j = 1).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4IncrementPrefixDelta ell M m H j = 0).card = ell - a) := by
  have hHlast :=
    aoyagiLemma4_Hlast_eq_zero_of_HtildeChainBounds ell a M m H ha hselected
      hlower hupper
  exact aoyagiLemma4_binaryIncrementPrefix_count_eq ell a M m H hH0 hHlast
    hselected hbin

/-- Same-coordinate vector-bound and binary-delta wrapper for the finite
Lemma 4-to-Lemma 3 free-count bridge.

The coordinate map is supplied.  This theorem does not prove Aoyagi's missing
source correspondence from a vector `T` to the chain `(H_j)`, nor does it prove
that source vectors have binary prefix deltas. -/
theorem aoyagiLemma4_sameCoordinateChain_binaryIncrementPrefixDelta_freeHighCount_lemma3A_eq_min
    (n a : ℕ) (M : ℤ) {ι : Type*}
    (m H : Fin (n + 2) → ℤ) (coord : Fin (n + 2) → ι)
    {Tlo T Thi : ι → ℤ}
    (hH0 : H 0 = m 0)
    (ha : a ≤ n + 1)
    (hselected : (∑ j : Fin (n + 2), m j) =
      ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hlo : Tlo ≤ T) (hhi : T ≤ Thi)
    (hlo_coord : ∀ j, Tlo (coord j) = aoyagiHtildeLowerChain (n + 1) a M m j)
    (hH_coord : ∀ j, T (coord j) = H j)
    (hhi_coord : ∀ j, Thi (coord j) = aoyagiHtildeUpperChain (n + 1) a M m j)
    (hbin : ∀ j : Fin (n + 1),
      aoyagiLemma4IncrementPrefixDelta (n + 1) M m H j = 0 ∨
        aoyagiLemma4IncrementPrefixDelta (n + 1) M m H j = 1) :
    aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
        ((Finset.univ.filter fun j : Fin n ↦
          aoyagiLemma4F (n + 1) m H j.castSucc = M).card : ℤ) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  have hlower : aoyagiHtildeLowerChain (n + 1) a M m ≤ H := by
    intro j
    rw [← hlo_coord j, ← hH_coord j]
    exact hlo (coord j)
  have hupper : H ≤ aoyagiHtildeUpperChain (n + 1) a M m := by
    intro j
    rw [← hH_coord j, ← hhi_coord j]
    exact hhi (coord j)
  exact
    aoyagiLemma4_HtildeChainBounds_freeHighCount_lemma3A_eq_min
      n a M m H hH0 ha hselected hlower hupper
      (aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta (n + 1) M m H hbin)

end Aoyagi
end DLN
end DLNFibre
