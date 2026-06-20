import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Two-value count arithmetic for Aoyagi's Lemma 4

This file isolates the finite counting step in Aoyagi's Lemma 4: if a finite
family has only the two values `lo` and `lo+1`, then the excess in its sum
counts the number of `lo+1` entries.  It does not formalise the vectors
`T_{s,k}`, the inequalities `Ttilde <= T <= Ttilde'`, feasibility, or the
claim that the vector corresponds to the RLCT candidate.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- If an integer-valued family has only the two values `lo` and `lo+1`, and
its sum is `ell*lo+a`, then exactly `a` entries are high and `ell-a` entries
are low. -/
theorem twoStepInt_count_eq (ell a : ℕ) (lo : ℤ) (v : Fin ell → ℤ)
    (hvals : ∀ i, v i = lo ∨ v i = lo + 1)
    (hsum : (∑ i : Fin ell, v i) = (ell : ℤ) * lo + a) :
    ((Finset.univ.filter fun i : Fin ell ↦ v i = lo + 1).card = a) ∧
      ((Finset.univ.filter fun i : Fin ell ↦ v i = lo).card = ell - a) := by
  classical
  let sHi : Finset (Fin ell) := Finset.univ.filter fun i : Fin ell ↦ v i = lo + 1
  have hpoint : ∀ i, v i = lo + if v i = lo + 1 then (1 : ℤ) else 0 := by
    intro i
    by_cases hhi : v i = lo + 1
    · simp [hhi]
    · rcases hvals i with hlo | hhi'
      · simp [hlo]
      · exact False.elim (hhi hhi')
  have hsum_eval : (∑ i : Fin ell, v i) = (ell : ℤ) * lo + (sHi.card : ℤ) := by
    calc
      (∑ i : Fin ell, v i)
          = ∑ i : Fin ell, (lo + if v i = lo + 1 then (1 : ℤ) else 0) := by
              exact Finset.sum_congr rfl (fun i _ ↦ hpoint i)
      _ = (∑ _i : Fin ell, lo) +
            ∑ i : Fin ell, (if v i = lo + 1 then (1 : ℤ) else 0) := by
              rw [Finset.sum_add_distrib]
      _ = (ell : ℤ) * lo + (sHi.card : ℤ) := by
              simp [sHi, Finset.sum_const, Fintype.card_fin]
  have hhi_card_int : (sHi.card : ℤ) = a := by
    omega
  have hhi_card : sHi.card = a := by
    exact_mod_cast hhi_card_int
  have hlow_eq_compl : (Finset.univ.filter fun i : Fin ell ↦ v i = lo) = sHiᶜ := by
    ext i
    simp only [sHi, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    constructor
    · intro hlo hhi
      omega
    · intro hnot_hi
      rcases hvals i with hlo | hhi
      · exact hlo
      · exact False.elim (hnot_hi hhi)
  constructor
  · simpa [sHi] using hhi_card
  · rw [hlow_eq_compl, Finset.card_compl, hhi_card]
    simp [Fintype.card_fin]

/-- The source-shaped two-value count used in Aoyagi's Lemma 4.  If each
`F_j` is either `M-1` or `M` and the sum is `ell*(M-1)+a`, then exactly `a`
entries are equal to `M` and exactly `ell-a` are equal to `M-1`.

This is only the finite count.  In the source proof, the sum identity itself
comes from the `H_ell=0` bookkeeping and is not proved here. -/
theorem aoyagiLemma4_twoValueCount_int (ell a : ℕ) (M : ℤ) (v : Fin ell → ℤ)
    (hvals : ∀ i, v i = M - 1 ∨ v i = M)
    (hsum : (∑ i : Fin ell, v i) = (ell : ℤ) * (M - 1) + a) :
    ((Finset.univ.filter fun i : Fin ell ↦ v i = M).card = a) ∧
      ((Finset.univ.filter fun i : Fin ell ↦ v i = M - 1).card = ell - a) := by
  have hvals' : ∀ i, v i = M - 1 ∨ v i = (M - 1) + 1 := by
    intro i
    rcases hvals i with hlo | hhi
    · exact Or.inl hlo
    · right
      omega
  have h := twoStepInt_count_eq ell a (M - 1) v hvals' hsum
  simpa [show (M - 1) + 1 = M by omega] using h

/-- The same hypotheses force the excess parameter `a` to lie in the interval
`0 <= a <= ell`. -/
theorem aoyagiLemma4_twoValueCount_le_ell (ell a : ℕ) (M : ℤ) (v : Fin ell → ℤ)
    (hvals : ∀ i, v i = M - 1 ∨ v i = M)
    (hsum : (∑ i : Fin ell, v i) = (ell : ℤ) * (M - 1) + a) :
    a ≤ ell := by
  have h := (aoyagiLemma4_twoValueCount_int ell a M v hvals hsum).1
  rw [← h]
  simpa [Fintype.card_fin] using
    Finset.card_le_univ (Finset.univ.filter fun i : Fin ell ↦ v i = M)

end Aoyagi
end DLN
end DLNFibre
