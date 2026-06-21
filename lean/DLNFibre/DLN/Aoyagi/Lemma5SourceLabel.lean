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

/-- Equation `(3)`'s label `k=Htilde'_1+1` is an actual source label when
the displayed one-unit width slack and actual-width compatibility are supplied.

Unlike equation `(4)`, the upper label bound for equation `(3)` is not a
consequence of Definition 3 alone; the slack `W_1+2<=M` is therefore explicit
through `hwidthGuards`. -/
theorem aoyagiLemma5Eq3_actualWidthLabel_of_widthCompatibility
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (ha_pos : 1 ≤ a) (ha_lt : a < ell)
    (hwidthGuards :
      M - 1 ≤ aoyagiSelectedWidthNat ell m 0 +
          aoyagiSelectedWidthNat ell m 1 ∧
        aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hs_le : C.point 1 - 1 ≤ L)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m 1 + 1) :
    actualWidthLabel L n (C.point 1 - 1) k := by
  have hlabel :=
    (aoyagiLemma5Eq3_localData_of_widthGuards
      ell a M m ha_pos ha_lt hwidthGuards).2.2
  have hS_pos : 1 ≤ C.point 1 - 1 := by
    have h0_pos : 1 ≤ C.point 0 := C.point_pos_of_lt (by omega)
    have hstrict : C.point 0 < C.point 1 := C.point_strict_succ (by omega)
    omega
  refine ⟨hS_pos, hs_le, ?_, ?_⟩
  · have hk_pos_int : (1 : ℤ) ≤ (k : ℤ) := by
      rw [hk]
      exact hlabel.1
    exact_mod_cast hk_pos_int
  · have hk_le_int : (k : ℤ) ≤ (n ((C.point 1 - 1) + 1) : ℤ) := by
      rw [hk, hwidth]
      exact hlabel.2
    exact_mod_cast hk_le_int

/-- Source-shaped equation `(3)` actual-label bridge: Definition 3 supplies
the lower label guard, while the missing one-unit slack remains explicit. -/
theorem aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (ha_pos : 1 ≤ a) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hs_le : C.point 1 - 1 ≤ L)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m 1 + 1) :
    actualWidthLabel L n (C.point 1 - 1) k := by
  have hlabel :=
    aoyagiHtildeUpperNat_one_add_one_labelBounds_of_sourceSelectedInequality_and_slack
      ell a M m hell ha ha_pos ha_lt hselected hsource hslack
  have hS_pos : 1 ≤ C.point 1 - 1 := by
    have h0_pos : 1 ≤ C.point 0 := C.point_pos_of_lt (by omega)
    have hstrict : C.point 0 < C.point 1 := C.point_strict_succ (by omega)
    omega
  refine ⟨hS_pos, hs_le, ?_, ?_⟩
  · have hk_pos_int : (1 : ℤ) ≤ (k : ℤ) := by
      rw [hk]
      exact hlabel.1
    exact_mod_cast hk_pos_int
  · have hk_le_int : (k : ℤ) ≤ (n ((C.point 1 - 1) + 1) : ℤ) := by
      rw [hk, hwidth]
      exact hlabel.2
    exact_mod_cast hk_le_int

/-- Equation `(5)`'s label `k=Htilde'_p+1-alpha` is an actual source label
when the selected width at `p` is identified with the actual layer width at
`S_(p+1)`.

This is only source-label arithmetic.  It assumes the Eq. `(5)` offset guards
`1<=alpha<=Htilde'_p-Htilde_p`; it does not construct the displayed vector,
prove terminality, chart coverage, pole order, normal crossings, or RLCT
extraction. -/
theorem aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hpell : p ≤ ell)
    (halpha_pos : 1 ≤ alpha)
    (halpha_le_excess : alpha ≤ aoyagiLemma5IntervalExcess ell a p)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hs_pos : 1 ≤ C.point p - 1) (hs_le : C.point p - 1 ≤ L)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    {k : ℕ} (hk :
      (k : ℤ) = aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    actualWidthLabel L n (C.point p - 1) k := by
  have hlabel :=
    aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality
      ell a p alpha M m hell ha hpell halpha_pos halpha_le_excess
      hselected hsource
  refine ⟨hs_pos, hs_le, ?_, ?_⟩
  · have hk_pos_int : (1 : ℤ) ≤ (k : ℤ) := by
      rw [hk]
      exact hlabel.1
    exact_mod_cast hk_pos_int
  · have hk_le_int : (k : ℤ) ≤ (n ((C.point p - 1) + 1) : ℤ) := by
      rw [hk, hwidth]
      exact hlabel.2
    exact_mod_cast hk_le_int

/-- Equation `(5)`'s label `k=Htilde'_p+1-alpha` is an actual source label at
an arbitrary source index `S`, when that index has actual width equal to the
selected width at coordinate `p`.

This is the arbitrary-source-index version of
`aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility`.  The source range and
width compatibility at `S` are explicit; no selected-block membership is needed
for label legality alone. -/
theorem aoyagiLemma5Eq5_actualWidthLabel_at_of_widthCompatibility
    (L ell a p alpha S : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hpell : p ≤ ell)
    (halpha_pos : 1 ≤ alpha)
    (halpha_le_excess : alpha ≤ aoyagiLemma5IntervalExcess ell a p)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hs_pos : 1 ≤ S) (hs_le : S ≤ L)
    (hwidth : (n (S + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    {k : ℕ} (hk :
      (k : ℤ) = aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    actualWidthLabel L n S k := by
  have hlabel :=
    aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality
      ell a p alpha M m hell ha hpell halpha_pos halpha_le_excess
      hselected hsource
  refine ⟨hs_pos, hs_le, ?_, ?_⟩
  · have hk_pos_int : (1 : ℤ) ≤ (k : ℤ) := by
      rw [hk]
      exact hlabel.1
    exact_mod_cast hk_pos_int
  · have hk_le_int : (k : ℤ) ≤ (n (S + 1) : ℤ) := by
      rw [hk, hwidth]
      exact hlabel.2
    exact_mod_cast hk_le_int

/-- A supplied equation `(5)` piecewise certificate gives the own-coordinate
value `k-1` and a legal actual source label under Definition 3 selected-width
hypotheses and actual-width compatibility.

The theorem remains conditional on the supplied piecewise certificate; it does
not construct equation `(5)`'s vector or prove terminal `tilde t=0`. -/
theorem aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hs_pos : 1 ≤ C.point p - 1) (hs_le : C.point p - 1 ≤ L)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {k : ℕ} (hk :
      (k : ℤ) = aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T (C.point p - 1) = (k : ℤ) - 1 ∧
      actualWidthLabel L n (C.point p - 1) k := by
  have hp_lt_ell : p < ell := by
    have hcut := hT.cutoffIndexGuard
    omega
  have hblock : C.block p (C.point p - 1) :=
    C.leftEndpoint_mem_block hp_lt_ell
  have hown :=
    aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
      ell a p alpha M m C layerWidth T hT
  constructor
  · exact aoyagiLemma5Eq5_ownCoordinate_eq_label_pred
      ell a p alpha M m C T hown hblock hk
  · exact aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility
      L ell a p alpha n M m C hell hT.a_le_ell (le_of_lt hp_lt_ell)
      hT.alpha_pos hT.alpha_le_excess hselected hsource hs_pos hs_le hwidth hk

/-- Arbitrary-own-block version of
`aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel`.

For any `S` in the own selected block `C.block p S`, a supplied equation `(5)`
piecewise certificate gives the value `T S=k-1`.  If the actual width at this
particular `S` is explicitly identified with the selected width `W_p`, then
the same source-label arithmetic proves `actualWidthLabel L n S k`. -/
theorem aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_block
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hs_pos : 1 ≤ S) (hs_le : S ≤ L)
    (hwidth : (n (S + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  have hown :=
    aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
      ell a p alpha M m C layerWidth T hT
  constructor
  · exact aoyagiLemma5Eq5_ownCoordinate_eq_label_pred
      ell a p alpha M m C T hown hS hk
  · exact aoyagiLemma5Eq5_actualWidthLabel_at_of_widthCompatibility
      L ell a p alpha S n M m hell hT.a_le_ell (le_of_lt hS.1)
      hT.alpha_pos hT.alpha_le_excess hselected hsource hs_pos hs_le hwidth hk

end Aoyagi
end DLN
end DLNFibre
