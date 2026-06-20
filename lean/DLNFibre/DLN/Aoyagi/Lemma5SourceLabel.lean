import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector

/-!
# Source-label bridges for Aoyagi's Lemma 5

This file connects the selected-width arithmetic around Aoyagi Lemma 5 to the
actual source-label predicate used by the blow-up bookkeeping.  It does not
construct displayed vectors, prove terminality, chart coverage, pole order,
normal crossings, or RLCT extraction.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Equation `(4)`'s label `k=Htilde_p+1` is an actual source label when the
selected width at `p` is identified with the actual layer width at
`S_(p+1)`.

The width compatibility is explicit: this theorem does not identify selected
widths with actual layer widths by itself. -/
theorem aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp0 : 1 ≤ p) (hp_a : p ≤ a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hs_pos : 1 ≤ C.point p - 1) (hs_le : C.point p - 1 ≤ L)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeLowerNat ell a M m p + 1) :
    actualWidthLabel L n (C.point p - 1) k := by
  have hlabel :=
    aoyagiHtildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
      ell a p M m hell ha hp0 hp_a hselected hsource
  refine ⟨hs_pos, hs_le, ?_, ?_⟩
  · have hk_pos_int : (1 : ℤ) ≤ (k : ℤ) := by
      rw [hk]
      exact hlabel.1
    exact_mod_cast hk_pos_int
  · have hk_le_int : (k : ℤ) ≤ (n ((C.point p - 1) + 1) : ℤ) := by
      rw [hk, hwidth]
      exact hlabel.2
    exact_mod_cast hk_le_int

end Aoyagi
end DLN
end DLNFibre
