import DLNFibre.DLN.Aoyagi.ArithmeticTail
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Two-value count arithmetic for Aoyagi's Lemma 4

This file isolates finite arithmetic in Aoyagi's Lemma 4: the source
`H`-bookkeeping telescope giving the increment sum, and the count saying that
if a finite family has only the two values `lo` and `lo+1`, then the excess in
its sum counts the number of `lo+1` entries.  It does not formalise the vectors
`T_{s,k}`, the inequalities `Ttilde <= T <= Ttilde'`, feasibility, or the
claim that the vector corresponds to the RLCT candidate.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Aoyagi's Lemma 4 finite increment
`F_j = H_{j-1} - H_j + M(S_{j+1})`, with the source's separate `F_1`
definition encoded by the convention `H_0 = M(S_1)`. -/
def aoyagiLemma4F (ell : ℕ) (m H : Fin (ell + 1) → ℤ) (j : Fin ell) : ℤ :=
  H j.castSucc - H j.succ + m j.succ

/-- For `ell = 2`, the first Lean increment is the source `F_1`. -/
example (m H : Fin 3 → ℤ) :
    aoyagiLemma4F 2 m H 0 = H 0 - H 1 + m 1 :=
  rfl

/-- For `ell = 2`, the second Lean increment is the source `F_2`. -/
example (m H : Fin 3 → ℤ) :
    aoyagiLemma4F 2 m H 1 = H 1 - H 2 + m 2 :=
  rfl

/-- The hidden telescoping sum in Aoyagi's Lemma 4.

If the uniform notation for `F_j` uses the convention `H_0 = M(S_1)`, and the
terminal condition is `H_ell = 0`, then the sum of the `F_j` equals the sum of
the selected widths `M(S_1),...,M(S_{ell+1})`. -/
theorem aoyagiLemma4F_sum_eq_selectedSum (ell : ℕ) (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0) (hHlast : H (Fin.last ell) = 0) :
    (∑ j : Fin ell, aoyagiLemma4F ell m H j) =
      ∑ j : Fin (ell + 1), m j := by
  have hsplit :
      (∑ j : Fin ell, aoyagiLemma4F ell m H j) =
        (∑ j : Fin ell, (H j.castSucc - H j.succ)) +
          ∑ j : Fin ell, m j.succ := by
    simp [aoyagiLemma4F, Finset.sum_add_distrib]
  have hHcast :
      (∑ j : Fin ell, H j.castSucc) =
        (∑ j : Fin (ell + 1), H j) - H (Fin.last ell) := by
    have h := Fin.sum_univ_castSucc (fun j : Fin (ell + 1) ↦ H j)
    omega
  have hHsucc :
      (∑ j : Fin ell, H j.succ) =
        (∑ j : Fin (ell + 1), H j) - H 0 := by
    have h := Fin.sum_univ_succ (fun j : Fin (ell + 1) ↦ H j)
    omega
  have htel :
      (∑ j : Fin ell, (H j.castSucc - H j.succ)) =
        H 0 - H (Fin.last ell) := by
    rw [Finset.sum_sub_distrib, hHcast, hHsucc]
    omega
  have hmTail :
      (∑ j : Fin ell, m j.succ) =
        (∑ j : Fin (ell + 1), m j) - m 0 := by
    have h := Fin.sum_univ_succ (fun j : Fin (ell + 1) ↦ m j)
    omega
  rw [hsplit, htel, hmTail, hH0, hHlast]
  omega

/-- Source-shaped sum identity bridge for Aoyagi's Lemma 4.

The hypothesis `hselected` is exactly Definition 3's arithmetic
`sum_j M(S_j) = ell*(M-1)+a`, stated over the selected indexed widths. The
conclusion removes the previously assumed `sum F_j` hypothesis, but still does
not prove the two-value condition or vector admissibility. -/
theorem aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a (ell a : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0) (hHlast : H (Fin.last ell) = 0)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    (∑ j : Fin ell, aoyagiLemma4F ell m H j) =
      (ell : ℤ) * (M - 1) + a := by
  rw [aoyagiLemma4F_sum_eq_selectedSum ell m H hH0 hHlast, hselected]

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

This is only the finite count.  The source proof's `H_ell=0` sum bridge is a
separate theorem, `aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a`. -/
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

/-- Lemma 4's count with the source `H`-bookkeeping sum bridge inlined.

This proves only the finite consequence of the terminal condition
`H_ell = 0`, the convention `H_0 = M(S_1)`, Definition 3's selected-width sum,
and the two-value hypothesis for the increments. It does not prove that an
arbitrary vector satisfies the two-value hypothesis or corresponds to
Aoyagi's `lambda`. -/
theorem aoyagiLemma4_twoValueCount_of_terminalH (ell a : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0) (hHlast : H (Fin.last ell) = 0)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hvals : ∀ j : Fin ell,
      aoyagiLemma4F ell m H j = M - 1 ∨ aoyagiLemma4F ell m H j = M) :
    ((Finset.univ.filter fun j : Fin ell ↦ aoyagiLemma4F ell m H j = M).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m H j = M - 1).card = ell - a) := by
  exact aoyagiLemma4_twoValueCount_int ell a M (aoyagiLemma4F ell m H) hvals
    (aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a ell a M m H hH0 hHlast
      hselected)

/-- The terminal-`H` hypotheses in the source-shaped Lemma 4 bridge force
`a <= ell` once the increments are known to be two-valued. -/
theorem aoyagiLemma4_twoValueCount_of_terminalH_le_ell (ell a : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0) (hHlast : H (Fin.last ell) = 0)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hvals : ∀ j : Fin ell,
      aoyagiLemma4F ell m H j = M - 1 ∨ aoyagiLemma4F ell m H j = M) :
    a ≤ ell := by
  exact aoyagiLemma4_twoValueCount_le_ell ell a M (aoyagiLemma4F ell m H) hvals
    (aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a ell a M m H hH0 hHlast
      hselected)

/-- Split a high-value count on `Fin (n+1)` into the first `n` positions and
the last position. -/
theorem highCount_castSucc_add_last_eq_total (n : ℕ) (M : ℤ)
    (v : Fin (n + 1) → ℤ) :
    ((Finset.univ.filter fun j : Fin n ↦ v j.castSucc = M).card) +
        (if v (Fin.last n) = M then 1 else 0) =
      (Finset.univ.filter fun j : Fin (n + 1) ↦ v j = M).card := by
  rw [Finset.card_filter, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]

/-- If exactly `a` of `n+1` positions are high, then the high-count on the
first `n` positions is either `a` or `a-1`, depending on the last position. -/
theorem highCount_castSucc_int_eq_or_eq_pred_of_total (n a : ℕ) (M : ℤ)
    (v : Fin (n + 1) → ℤ)
    (hcount : (Finset.univ.filter fun j : Fin (n + 1) ↦ v j = M).card = a) :
    (((Finset.univ.filter fun j : Fin n ↦ v j.castSucc = M).card : ℤ) =
        (a : ℤ)) ∨
      (((Finset.univ.filter fun j : Fin n ↦ v j.castSucc = M).card : ℤ) =
        (a : ℤ) - 1) := by
  have hsplit := highCount_castSucc_add_last_eq_total n M v
  rw [hcount] at hsplit
  by_cases hlast : v (Fin.last n) = M
  · right
    simp [hlast] at hsplit
    omega
  · left
    simp [hlast] at hsplit
    omega

/-- The free high-count used in the Lemma 3 quadratic is one of Lemma 3's
two equality cases, once Lemma 4 has counted `a` high increments among all
`n+1` increments.

This is only the finite count-to-Lemma-3 bridge.  It does not prove that the
increments come from admissible exponent vectors, or that the quadratic is the
source terminal exponent expression. -/
theorem aoyagiLemma4_freeHighCount_lemma3A_eq_min_of_totalCount (n a : ℕ) (M : ℤ)
    (v : Fin (n + 1) → ℤ)
    (hcount : (Finset.univ.filter fun j : Fin (n + 1) ↦ v j = M).card = a) :
    aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
        ((Finset.univ.filter fun j : Fin n ↦ v j.castSucc = M).card : ℤ) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  have hcases := highCount_castSucc_int_eq_or_eq_pred_of_total n a M v hcount
  exact (aoyagiLemma3A_eq_min_iff ((n + 1 : ℕ) : ℤ) (a : ℤ)
    ((Finset.univ.filter fun j : Fin n ↦ v j.castSucc = M).card : ℤ)
    (by omega)).mpr hcases

/-- Source-shaped version of the finite Lemma 4-to-Lemma 3 bridge.

With the terminal-`H` sum bridge and the two-value increment hypothesis,
the number of high increments among the first `n` free positions attains the
isolated Lemma 3 numerator minimum for `ell = n+1`.  This remains finite
arithmetic only: it does not prove the two-value hypothesis, vector
admissibility, terminal exponent rewriting, or correspondence to `lambda`. -/
theorem aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min (n a : ℕ) (M : ℤ)
    (m H : Fin (n + 2) → ℤ)
    (hH0 : H 0 = m 0) (hHlast : H (Fin.last (n + 1)) = 0)
    (hselected : (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hvals : ∀ j : Fin (n + 1),
      aoyagiLemma4F (n + 1) m H j = M - 1 ∨ aoyagiLemma4F (n + 1) m H j = M) :
    aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
        ((Finset.univ.filter fun j : Fin n ↦
          aoyagiLemma4F (n + 1) m H j.castSucc = M).card : ℤ) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  have hcount :=
    (aoyagiLemma4_twoValueCount_of_terminalH (n + 1) a M m H hH0 hHlast
      hselected hvals).1
  exact aoyagiLemma4_freeHighCount_lemma3A_eq_min_of_totalCount n a M
    (aoyagiLemma4F (n + 1) m H) hcount

/-- Common endpoint expression for Aoyagi's displayed `Htilde_ell` and
`Htilde'_ell`.

This is only the terminal value.  It does not define the full `Htilde` or
`Htilde'` chains. -/
def aoyagiLemma4TerminalEndpoint (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) : ℤ :=
  (∑ j : Fin (ell + 1), m j) -
    ((a : ℤ) * M + ((ell - a : ℕ) : ℤ) * (M - 1))

/-- The displayed terminal endpoints `Htilde_ell` and `Htilde'_ell` vanish
under Definition 3's selected-width sum. -/
theorem aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum (ell a : ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a) :
    aoyagiLemma4TerminalEndpoint ell a M m = 0 := by
  unfold aoyagiLemma4TerminalEndpoint
  rw [hselected]
  rw [Nat.cast_sub ha]
  ring

/-- If a terminal `H_ell` is squeezed between Aoyagi's two displayed terminal
endpoints, then it is zero once those endpoints have been identified with
zero. -/
theorem aoyagiLemma4_Hlast_eq_zero_of_terminalEndpoint_bounds
    {ell a : ℕ} {M : ℤ} {m H : Fin (ell + 1) → ℤ}
    (hend : aoyagiLemma4TerminalEndpoint ell a M m = 0)
    (hlower : aoyagiLemma4TerminalEndpoint ell a M m ≤ H (Fin.last ell))
    (hupper : H (Fin.last ell) ≤ aoyagiLemma4TerminalEndpoint ell a M m) :
    H (Fin.last ell) = 0 := by
  omega

/-- Lemma 4's count with the source endpoint sandwich replacing the explicit
terminal condition `H_ell = 0`.

This is still finite arithmetic only.  It assumes the endpoint sandwich and the
two-value increment hypothesis; it does not prove either from vector
admissibility. -/
theorem aoyagiLemma4_twoValueCount_of_terminalEndpointBounds (ell a : ℕ) (M : ℤ)
    (m H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hlower : aoyagiLemma4TerminalEndpoint ell a M m ≤ H (Fin.last ell))
    (hupper : H (Fin.last ell) ≤ aoyagiLemma4TerminalEndpoint ell a M m)
    (hvals : ∀ j : Fin ell,
      aoyagiLemma4F ell m H j = M - 1 ∨ aoyagiLemma4F ell m H j = M) :
    ((Finset.univ.filter fun j : Fin ell ↦ aoyagiLemma4F ell m H j = M).card = a) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m H j = M - 1).card = ell - a) := by
  have hend := aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum ell a M m ha hselected
  have hHlast :=
    aoyagiLemma4_Hlast_eq_zero_of_terminalEndpoint_bounds hend hlower hupper
  exact aoyagiLemma4_twoValueCount_of_terminalH ell a M m H hH0 hHlast hselected hvals

/-- Source-shaped endpoint-sandwich wrapper for the finite Lemma 4-to-Lemma 3
free-count bridge. -/
theorem aoyagiLemma4_terminalEndpointBounds_freeHighCount_lemma3A_eq_min
    (n a : ℕ) (M : ℤ) (m H : Fin (n + 2) → ℤ)
    (hH0 : H 0 = m 0)
    (ha : a ≤ n + 1)
    (hselected : (∑ j : Fin (n + 2), m j) =
      ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    (hlower :
      aoyagiLemma4TerminalEndpoint (n + 1) a M m ≤ H (Fin.last (n + 1)))
    (hupper :
      H (Fin.last (n + 1)) ≤ aoyagiLemma4TerminalEndpoint (n + 1) a M m)
    (hvals : ∀ j : Fin (n + 1),
      aoyagiLemma4F (n + 1) m H j = M - 1 ∨
        aoyagiLemma4F (n + 1) m H j = M) :
    aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
        ((Finset.univ.filter fun j : Fin n ↦
          aoyagiLemma4F (n + 1) m H j.castSucc = M).card : ℤ) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  have hend :=
    aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum (n + 1) a M m ha hselected
  have hHlast :=
    aoyagiLemma4_Hlast_eq_zero_of_terminalEndpoint_bounds hend hlower hupper
  exact aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min n a M m H hH0
    hHlast hselected hvals

end Aoyagi
end DLN
end DLNFibre
