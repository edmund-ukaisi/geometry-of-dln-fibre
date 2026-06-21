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

/-- A supplied equation `(4)` piecewise certificate gives the own-coordinate
value `k-1` and a legal actual source label under the repaired guards and
actual-width compatibility.

This is only an adapter combining the already-proved equation `(4)` value
theorem with the actual-label bridge.  It does not construct the displayed
vector or prove terminality. -/
theorem aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_widthCompatibility
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hs_pos : 1 ≤ C.point p - 1) (hs_le : C.point p - 1 ≤ L)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeLowerNat ell a M m p + 1) :
    T (C.point p - 1) = (k : ℤ) - 1 ∧
      actualWidthLabel L n (C.point p - 1) k := by
  have hown :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
      ell a p M m C layerWidth T hell hp0 hp_c hselected hsource hT
  have hp_a : p ≤ a := by
    have hp_tail := hT.indexGuard
    omega
  constructor
  · rw [hown.2.1, hk]
    ring
  · exact aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility
      L ell a p n M m C hell hT.a_le_ell hp0 hp_a hselected hsource
      hs_pos hs_le hwidth hk

/-- A supplied equation `(3)` piecewise certificate gives the own-coordinate
value `k-1` and a legal actual source label when the explicit one-unit slack
and actual-width compatibility are supplied.

This is only an adapter combining the already-proved equation `(3)` value
theorem with the actual-label bridge.  It does not construct the displayed
vector or prove terminality. -/
theorem aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_sourceSelected_slack
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hs_le : C.point 1 - 1 ≤ L)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m 1 + 1) :
    T (C.point 1 - 1) = (k : ℤ) - 1 ∧
      actualWidthLabel L n (C.point 1 - 1) k := by
  have hown :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
      ell a M m C layerWidth T hell ha_lt hselected hsource hslack hT
  constructor
  · rw [hown.2.1, hk]
    ring
  · exact aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack
      L ell a n M m C hell hT.a_le_ell hT.indexGuard ha_lt hselected hsource
      hslack hs_le hwidth hk

/-- Last-cutpoint source-range wrapper for equation `(4)`'s own-coordinate
actual label.

The last-cutpoint compatibility `C.point ell<=L+1` supplies the upper source
range for the own selected source layer.  Actual-width compatibility at that
source layer remains explicit. -/
theorem aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeLowerNat ell a M m p + 1) :
    T (C.point p - 1) = (k : ℤ) - 1 ∧
      actualWidthLabel L n (C.point p - 1) k := by
  have hp_lt_ell : p < ell := by
    have ha : a ≤ ell := hT.a_le_ell
    have hp_tail : p + 1 ≤ a := hT.indexGuard
    omega
  have hblock : C.block p (C.point p - 1) :=
    C.leftEndpoint_mem_block hp_lt_ell
  have hs_pos : 1 ≤ C.point p - 1 := by
    have hp_pos : 0 < p := by omega
    have hpoint0_pos : 1 ≤ C.point 0 := C.point_pos_of_lt (by omega)
    have hstrict : C.point 0 < C.point p :=
      C.point_strict_of_lt hp_pos (by omega)
    omega
  have hs_le : C.point p - 1 ≤ L :=
    C.block_sourceIndex_le_of_lastPoint_le hblock hlast
  exact aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_widthCompatibility
    L ell a p n M m C layerWidth T hell hp0 hp_c hselected hsource
    hs_pos hs_le hwidth hT hk

/-- Last-cutpoint source-range wrapper for equation `(3)`'s own-coordinate
actual label.

The last-cutpoint compatibility `C.point ell<=L+1` supplies the upper source
range for `S_2-1`.  Actual-width compatibility and the equation `(3)` slack
remain explicit. -/
theorem aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m 1 + 1) :
    T (C.point 1 - 1) = (k : ℤ) - 1 ∧
      actualWidthLabel L n (C.point 1 - 1) k := by
  have ha_pos : 1 ≤ a := hT.indexGuard
  have h1_lt : 1 < ell := by omega
  have hblock : C.block 1 (C.point 1 - 1) :=
    C.leftEndpoint_mem_block h1_lt
  have hs_le : C.point 1 - 1 ≤ L :=
    C.block_sourceIndex_le_of_lastPoint_le hblock hlast
  exact aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_sourceSelected_slack
    L ell a n M m C layerWidth T hell ha_lt hselected hsource hslack
    hs_le hwidth hT hk

/-- Eq3-shaped component actual-label wrapper under supplied label bounds.

This p-general wrapper deliberately does not derive the label bounds from
Definition 3.  It only combines the supplied Eq3-shaped component value with
explicit source-range, actual-width, and label-bound hypotheses. -/
theorem aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hlabelBounds :
      (1 : ℤ) ≤ aoyagiHtildeUpperNat ell a M m p + 1 ∧
        aoyagiHtildeUpperNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m p + 1) :
    T (C.point p - 1) = (k : ℤ) - 1 ∧
      actualWidthLabel L n (C.point p - 1) k := by
  have hp_lt_ell : p < ell := by
    have ha : a ≤ ell := hT.a_le_ell
    have ha_pos : 1 ≤ a := hT.indexGuard
    omega
  have hblock : C.block p (C.point p - 1) :=
    C.leftEndpoint_mem_block hp_lt_ell
  have hS_pos : 1 ≤ C.point p - 1 := by
    have hp0 : 0 < p := by omega
    have hpoint0_pos : 1 ≤ C.point 0 := C.point_pos_of_lt (by omega)
    have hstrict : C.point 0 < C.point p :=
      C.point_strict_of_lt hp0 (by omega)
    omega
  have hS_le : C.point p - 1 ≤ L :=
    C.block_sourceIndex_le_of_lastPoint_le hblock hlast
  have hcomponent :=
    aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap
      ell a p M m C layerWidth T hp_pos hp_c hT
  constructor
  · rw [hcomponent, hk]
    ring
  · refine ⟨hS_pos, hS_le, ?_, ?_⟩
    · have hk_pos_int : (1 : ℤ) ≤ (k : ℤ) := by
        rw [hk]
        exact hlabelBounds.1
      exact_mod_cast hk_pos_int
    · have hk_le_int : (k : ℤ) ≤ (n ((C.point p - 1) + 1) : ℤ) := by
        rw [hk, hwidth]
        exact hlabelBounds.2
      exact_mod_cast hk_le_int

/-- Eq3-shaped component wrapper with post-advance introduced-label
membership under supplied label bounds. -/
theorem aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hlabelBounds :
      (1 : ℤ) ≤ aoyagiHtildeUpperNat ell a M m p + 1 ∧
        aoyagiHtildeUpperNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m p + 1) :
    T (C.point p - 1) = (k : ℤ) - 1 ∧
      introducedLabel L n (C.point p - 1) k (C.point p - 1) k := by
  have hlabel :=
    aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
      L ell a p n M m C layerWidth T hp_pos hp_c hlast hwidth
      hlabelBounds hT hk
  exact ⟨hlabel.1, introducedLabel_of_eq_stage_le hlabel.2 rfl le_rfl⟩

/-- Finite-domain version of
`aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds`. -/
theorem aoyagiLemma5Eq3_component_mem_introducedLabelFinset_of_lastPoint_labelBounds
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hlabelBounds :
      (1 : ℤ) ≤ aoyagiHtildeUpperNat ell a M m p + 1 ∧
        aoyagiHtildeUpperNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m p + 1) :
    T (C.point p - 1) = (k : ℤ) - 1 ∧
      Sigma.mk (C.point p - 1) k ∈
        introducedLabelFinset L n (C.point p - 1) k := by
  have h :=
    aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds
      L ell a p n M m C layerWidth T hp_pos hp_c hlast hwidth
      hlabelBounds hT hk
  exact ⟨h.1, mem_introducedLabelFinset.mpr h.2⟩

/-- Eq3-shaped component wrapper with interval membership and finite-domain
introduced-label membership under supplied label bounds. -/
theorem aoyagiLemma5Eq3_component_intervalValue_mem_introducedLabelFinset_of_lastPoint_labelBounds
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hlabelBounds :
      (1 : ℤ) ≤ aoyagiHtildeUpperNat ell a M m p + 1 ∧
        aoyagiHtildeUpperNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m p + 1) :
    T (C.point p - 1) ∈ aoyagiHtildeIntervalValueSetNat ell a M m p ∧
      T (C.point p - 1) = (k : ℤ) - 1 ∧
        Sigma.mk (C.point p - 1) k ∈
          introducedLabelFinset L n (C.point p - 1) k := by
  have hcomponent :=
    aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap
      ell a p M m C layerWidth T hp_pos hp_c hT
  have hfinite :=
    aoyagiLemma5Eq3_component_mem_introducedLabelFinset_of_lastPoint_labelBounds
      L ell a p n M m C layerWidth T hp_pos hp_c hlast hwidth
      hlabelBounds hT hk
  refine ⟨?_, hfinite.1, hfinite.2⟩
  have hp_lt : p < ell + 1 := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  rw [hcomponent]
  exact aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
    ell a p M m hT.a_le_ell hp_lt

/-- Eq3-shaped component one-step introduced-label finite-domain update under
supplied label bounds.

This is finite-domain bookkeeping for the p-general Eq3-shaped upper component.
It does not derive the label bounds from Definition 3 or construct displayed
vectors. -/
theorem aoyagiLemma5Eq3_componentFinset_succ_eq_insert_of_lastPoint_labelBounds
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hlabelBounds :
      (1 : ℤ) ≤ aoyagiHtildeUpperNat ell a M m p + 1 ∧
        aoyagiHtildeUpperNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1) :
    introducedLabelFinset L n (C.point p - 1) (J + 1) =
      insert (Sigma.mk (C.point p - 1) (J + 1))
        (introducedLabelFinset L n (C.point p - 1) J) := by
  have hlabel :=
    aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
      L ell a p n M m C layerWidth T hp_pos hp_c hlast hwidth
      hlabelBounds hT hJ
  exact introducedLabelFinset_succ_eq_insert hlabel.2

/-- Cardinality form of
`aoyagiLemma5Eq3_componentFinset_succ_eq_insert_of_lastPoint_labelBounds`. -/
theorem aoyagiLemma5Eq3_componentFinset_card_succ_eq_succ_of_lastPoint_labelBounds
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hlabelBounds :
      (1 : ℤ) ≤ aoyagiHtildeUpperNat ell a M m p + 1 ∧
        aoyagiHtildeUpperNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1) :
    (introducedLabelFinset L n (C.point p - 1) (J + 1)).card =
      (introducedLabelFinset L n (C.point p - 1) J).card + 1 := by
  have hlabel :=
    aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
      L ell a p n M m C layerWidth T hp_pos hp_c hlast hwidth
      hlabelBounds hT hJ
  exact introducedLabelFinset_card_succ_eq_succ hlabel.2

/-- Source-facing Eq3 component specialization of the supplied Case 2
recurrence-weight update.

For one Eq3-shaped upper component whose label is `J+1`, a supplied successor
recurrence state with the standard Case 2 post-data has row weights multiplied
by the new variable from row `J+1` onward.  This is conditional recurrence
bookkeeping, not chart production. -/
theorem aoyagiLemma5Eq3_component_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_labelBounds
    {α : Type*} [CommMonoid α]
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hlabelBounds :
      (1 : ℤ) ≤ aoyagiHtildeUpperNat ell a M m p + 1 ∧
        aoyagiHtildeUpperNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1)
    {pre : IntroducedLabelRecurrenceState L n (C.point p - 1) J α}
    {post : IntroducedLabelRecurrenceState L n (C.point p - 1) (J + 1) α}
    {u : α}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u) :
    ∀ i, J + 1 ≤ i → post.weight i = u * pre.weight i := by
  have hlabel :=
    aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
      L ell a p n M m C layerWidth T hp_pos hp_c hlast hwidth
      hlabelBounds hT hJ
  exact fun i hi ↦ hpost.weight_succ_current_eq_new_mul_of_ge hlabel.2 hi

/-- Source-facing Eq3 component supplied exponent-domain extension.

For one Eq3-shaped upper component whose label is `J+1`, the source-label
wrapper supplies only the new label's introduced-label field.  The terminal
exponent and least-value fields are supplied explicitly; this theorem only
routes them through the generic one-step exponent-certificate domain
extension. -/
theorem aoyagiLemma5Eq3_component_extendExponentDomain_succ_current_of_lastPoint_labelBounds
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hlabelBounds :
      (1 : ℤ) ≤ aoyagiHtildeUpperNat ell a M m p + 1 ∧
        aoyagiHtildeUpperNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1)
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates
      L n (C.point p - 1) J t numerator leastValue)
    (hterminal :
      terminalExponent L (widthZ n) (t' (C.point p - 1) (J + 1)) =
        numerator' (C.point p - 1) (J + 1))
    (hleast :
      IsLeast
        {v : ℤ | ∃ i, i ∈ Finset.Icc 1 L ∧
          t' (C.point p - 1) (J + 1) i = v}
        (leastValue' (C.point p - 1) (J + 1)))
    (ht_old : ∀ {s k}, introducedLabel L n (C.point p - 1) J s k →
      t' s k = t s k)
    (hn_old : ∀ {s k}, introducedLabel L n (C.point p - 1) J s k →
      numerator' s k = numerator s k)
    (hl_old : ∀ {s k}, introducedLabel L n (C.point p - 1) J s k →
      leastValue' s k = leastValue s k) :
    IntroducedLabelExponentCertificates
      L n (C.point p - 1) (J + 1) t' numerator' leastValue' := by
  have hlabel :=
    aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
      L ell a p n M m C layerWidth T hp_pos hp_c hlast hwidth
      hlabelBounds hT hJ
  have hnew :
      LabelExponentCertificate L n (C.point p - 1) (J + 1)
        (C.point p - 1) (J + 1)
        (t' (C.point p - 1) (J + 1))
        (numerator' (C.point p - 1) (J + 1))
        (leastValue' (C.point p - 1) (J + 1)) := by
    refine
      { introduced := ?_
        terminalExponent_eq := hterminal
        least_value := hleast }
    exact introducedLabel_of_eq_stage_le hlabel.2 rfl le_rfl
  exact hcert.extendDomain_succ_current hnew ht_old hn_old hl_old

/-- Equation `(4)` own-coordinate wrapper with post-advance introduced-label
membership.

The state is `(S,k)` for `S=C.point p-1`: the supplied branch gives
`T S=k-1`, while the actual source label is introduced after advancing through
label `k`. -/
theorem aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeLowerNat ell a M m p + 1) :
    T (C.point p - 1) = (k : ℤ) - 1 ∧
      introducedLabel L n (C.point p - 1) k (C.point p - 1) k := by
  have hlabel :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a p n M m C layerWidth T hell hp0 hp_c hselected hsource hlast
      hwidth hT hk
  exact ⟨hlabel.1, introducedLabel_of_eq_stage_le hlabel.2 rfl le_rfl⟩

/-- Finite-domain version of
`aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint`. -/
theorem aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeLowerNat ell a M m p + 1) :
    T (C.point p - 1) = (k : ℤ) - 1 ∧
      Sigma.mk (C.point p - 1) k ∈
        introducedLabelFinset L n (C.point p - 1) k := by
  have h :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint
      L ell a p n M m C layerWidth T hell hp0 hp_c hselected hsource hlast
      hwidth hT hk
  exact ⟨h.1, mem_introducedLabelFinset.mpr h.2⟩

/-- Equation `(4)` own-coordinate one-step introduced-label finite-domain update.

This is finite-domain bookkeeping for a supplied endpoint branch.  It keeps
actual-width compatibility explicit and does not construct displayed vectors or
prove an order count. -/
theorem aoyagiLemma5Eq4_ownCoordinateFinset_succ_eq_insert_of_lastPoint
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeLowerNat ell a M m p + 1) :
    introducedLabelFinset L n (C.point p - 1) (J + 1) =
      insert (Sigma.mk (C.point p - 1) (J + 1))
        (introducedLabelFinset L n (C.point p - 1) J) := by
  have hlabel :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a p n M m C layerWidth T hell hp0 hp_c hselected hsource hlast
      hwidth hT hJ
  exact introducedLabelFinset_succ_eq_insert hlabel.2

/-- Cardinality form of
`aoyagiLemma5Eq4_ownCoordinateFinset_succ_eq_insert_of_lastPoint`. -/
theorem aoyagiLemma5Eq4_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeLowerNat ell a M m p + 1) :
    (introducedLabelFinset L n (C.point p - 1) (J + 1)).card =
      (introducedLabelFinset L n (C.point p - 1) J).card + 1 := by
  have hlabel :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a p n M m C layerWidth T hell hp0 hp_c hselected hsource hlast
      hwidth hT hJ
  exact introducedLabelFinset_card_succ_eq_succ hlabel.2

/-- Source-facing Eq4 specialization of the supplied Case 2 recurrence-weight
update.

For one supplied Eq4 endpoint branch whose label is `J+1`, a supplied
successor recurrence state with the standard Case 2 post-data has row weights
multiplied by the new variable from row `J+1` onward.  This is conditional
recurrence bookkeeping and does not assert that a blow-up chart produces the
post-state. -/
theorem aoyagiLemma5Eq4_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint
    {α : Type*} [CommMonoid α]
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeLowerNat ell a M m p + 1)
    {pre : IntroducedLabelRecurrenceState L n (C.point p - 1) J α}
    {post : IntroducedLabelRecurrenceState L n (C.point p - 1) (J + 1) α}
    {u : α}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u) :
    ∀ i, J + 1 ≤ i → post.weight i = u * pre.weight i := by
  have hlabel :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a p n M m C layerWidth T hell hp0 hp_c hselected hsource hlast
      hwidth hT hJ
  exact fun i hi ↦ hpost.weight_succ_current_eq_new_mul_of_ge hlabel.2 hi

/-- Source-facing Eq4 supplied exponent-domain extension.

For one supplied Eq4 endpoint branch whose label is `J+1`, the existing
source-label wrapper supplies the new label's introduced-label field.  The
terminal exponent and least-value fields are supplied explicitly; this theorem
only routes them through the generic one-step exponent-certificate domain
extension. -/
theorem aoyagiLemma5Eq4_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeLowerNat ell a M m p + 1)
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates
      L n (C.point p - 1) J t numerator leastValue)
    (hterminal :
      terminalExponent L (widthZ n) (t' (C.point p - 1) (J + 1)) =
        numerator' (C.point p - 1) (J + 1))
    (hleast :
      IsLeast
        {v : ℤ | ∃ i, i ∈ Finset.Icc 1 L ∧
          t' (C.point p - 1) (J + 1) i = v}
        (leastValue' (C.point p - 1) (J + 1)))
    (ht_old : ∀ {s k}, introducedLabel L n (C.point p - 1) J s k →
      t' s k = t s k)
    (hn_old : ∀ {s k}, introducedLabel L n (C.point p - 1) J s k →
      numerator' s k = numerator s k)
    (hl_old : ∀ {s k}, introducedLabel L n (C.point p - 1) J s k →
      leastValue' s k = leastValue s k) :
    IntroducedLabelExponentCertificates
      L n (C.point p - 1) (J + 1) t' numerator' leastValue' := by
  have hlabel :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a p n M m C layerWidth T hell hp0 hp_c hselected hsource hlast
      hwidth hT hJ
  have hnew :
      LabelExponentCertificate L n (C.point p - 1) (J + 1)
        (C.point p - 1) (J + 1)
        (t' (C.point p - 1) (J + 1))
        (numerator' (C.point p - 1) (J + 1))
        (leastValue' (C.point p - 1) (J + 1)) := by
    refine
      { introduced := ?_
        terminalExponent_eq := hterminal
        least_value := hleast }
    exact introducedLabel_of_eq_stage_le hlabel.2 rfl le_rfl
  exact hcert.extendDomain_succ_current hnew ht_old hn_old hl_old

/-- Equation `(4)` own-coordinate wrapper with interval membership and
finite-domain introduced-label membership.

This adds only the same-coordinate interval membership for the supplied lower
endpoint value.  It remains a supplied-piecewise adapter, not a construction
or terminality theorem. -/
theorem aoyagiLemma5Eq4_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint
    (L ell a p : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point p - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeLowerNat ell a M m p + 1) :
    T (C.point p - 1) ∈ aoyagiHtildeIntervalValueSetNat ell a M m p ∧
      T (C.point p - 1) = (k : ℤ) - 1 ∧
        Sigma.mk (C.point p - 1) k ∈
          introducedLabelFinset L n (C.point p - 1) k := by
  have hown :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
      ell a p M m C layerWidth T hell hp0 hp_c hselected hsource hT
  have hfinite :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
      L ell a p n M m C layerWidth T hell hp0 hp_c hselected hsource hlast
      hwidth hT hk
  refine ⟨?_, hfinite.1, hfinite.2⟩
  have hp_lt : p < ell + 1 := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  rw [hown.2.1]
  exact aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt
    ell a p M m hT.a_le_ell hp_lt

/-- Equation `(3)` own-coordinate wrapper with post-advance introduced-label
membership.

The explicit slack and actual-width compatibility are inherited from the
actual-label wrapper.  This remains a supplied-piecewise adapter, not a
displayed-vector construction. -/
theorem aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m 1 + 1) :
    T (C.point 1 - 1) = (k : ℤ) - 1 ∧
      introducedLabel L n (C.point 1 - 1) k (C.point 1 - 1) k := by
  have hlabel :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a n M m C layerWidth T hell ha_lt hselected hsource hslack hlast
      hwidth hT hk
  exact ⟨hlabel.1, introducedLabel_of_eq_stage_le hlabel.2 rfl le_rfl⟩

/-- Finite-domain version of
`aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint`. -/
theorem aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m 1 + 1) :
    T (C.point 1 - 1) = (k : ℤ) - 1 ∧
      Sigma.mk (C.point 1 - 1) k ∈
        introducedLabelFinset L n (C.point 1 - 1) k := by
  have h :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint
      L ell a n M m C layerWidth T hell ha_lt hselected hsource hslack hlast
      hwidth hT hk
  exact ⟨h.1, mem_introducedLabelFinset.mpr h.2⟩

/-- Equation `(3)` own-coordinate one-step introduced-label finite-domain update.

The explicit one-unit slack and actual-width compatibility are inherited from
the source-label wrapper.  This remains bookkeeping for a supplied endpoint
branch, not a displayed-vector construction or order-count theorem. -/
theorem aoyagiLemma5Eq3_ownCoordinateFinset_succ_eq_insert_of_lastPoint
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m 1 + 1) :
    introducedLabelFinset L n (C.point 1 - 1) (J + 1) =
      insert (Sigma.mk (C.point 1 - 1) (J + 1))
        (introducedLabelFinset L n (C.point 1 - 1) J) := by
  have hlabel :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a n M m C layerWidth T hell ha_lt hselected hsource hslack hlast
      hwidth hT hJ
  exact introducedLabelFinset_succ_eq_insert hlabel.2

/-- Cardinality form of
`aoyagiLemma5Eq3_ownCoordinateFinset_succ_eq_insert_of_lastPoint`. -/
theorem aoyagiLemma5Eq3_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m 1 + 1) :
    (introducedLabelFinset L n (C.point 1 - 1) (J + 1)).card =
      (introducedLabelFinset L n (C.point 1 - 1) J).card + 1 := by
  have hlabel :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a n M m C layerWidth T hell ha_lt hselected hsource hslack hlast
      hwidth hT hJ
  exact introducedLabelFinset_card_succ_eq_succ hlabel.2

/-- Source-facing Eq3 specialization of the supplied Case 2 recurrence-weight
update.

For one supplied Eq3 endpoint branch whose label is `J+1`, a supplied
successor recurrence state with the standard Case 2 post-data has row weights
multiplied by the new variable from row `J+1` onward.  The explicit one-unit
slack and actual-width compatibility are inherited from the source-label
wrapper.  This is conditional recurrence bookkeeping and does not assert that a
blow-up chart produces the post-state. -/
theorem aoyagiLemma5Eq3_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint
    {α : Type*} [CommMonoid α]
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m 1 + 1)
    {pre : IntroducedLabelRecurrenceState L n (C.point 1 - 1) J α}
    {post : IntroducedLabelRecurrenceState L n (C.point 1 - 1) (J + 1) α}
    {u : α}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u) :
    ∀ i, J + 1 ≤ i → post.weight i = u * pre.weight i := by
  have hlabel :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a n M m C layerWidth T hell ha_lt hselected hsource hslack hlast
      hwidth hT hJ
  exact fun i hi ↦ hpost.weight_succ_current_eq_new_mul_of_ge hlabel.2 hi

/-- Source-facing Eq3 supplied exponent-domain extension.

For one supplied Eq3 endpoint branch whose label is `J+1`, the existing
source-label wrapper supplies the new label's introduced-label field.  The
terminal exponent and least-value fields are supplied explicitly; this theorem
only routes them through the generic one-step exponent-certificate domain
extension. -/
theorem aoyagiLemma5Eq3_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {J : ℕ} (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m 1 + 1)
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates
      L n (C.point 1 - 1) J t numerator leastValue)
    (hterminal :
      terminalExponent L (widthZ n) (t' (C.point 1 - 1) (J + 1)) =
        numerator' (C.point 1 - 1) (J + 1))
    (hleast :
      IsLeast
        {v : ℤ | ∃ i, i ∈ Finset.Icc 1 L ∧
          t' (C.point 1 - 1) (J + 1) i = v}
        (leastValue' (C.point 1 - 1) (J + 1)))
    (ht_old : ∀ {s k}, introducedLabel L n (C.point 1 - 1) J s k →
      t' s k = t s k)
    (hn_old : ∀ {s k}, introducedLabel L n (C.point 1 - 1) J s k →
      numerator' s k = numerator s k)
    (hl_old : ∀ {s k}, introducedLabel L n (C.point 1 - 1) J s k →
      leastValue' s k = leastValue s k) :
    IntroducedLabelExponentCertificates
      L n (C.point 1 - 1) (J + 1) t' numerator' leastValue' := by
  have hlabel :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
      L ell a n M m C layerWidth T hell ha_lt hselected hsource hslack hlast
      hwidth hT hJ
  have hnew :
      LabelExponentCertificate L n (C.point 1 - 1) (J + 1)
        (C.point 1 - 1) (J + 1)
        (t' (C.point 1 - 1) (J + 1))
        (numerator' (C.point 1 - 1) (J + 1))
        (leastValue' (C.point 1 - 1) (J + 1)) := by
    refine
      { introduced := ?_
        terminalExponent_eq := hterminal
        least_value := hleast }
    exact introducedLabel_of_eq_stage_le hlabel.2 rfl le_rfl
  exact hcert.extendDomain_succ_current hnew ht_old hn_old hl_old

/-- Equation `(3)` own-coordinate wrapper with interval membership and
finite-domain introduced-label membership.

The interval value is the upper endpoint at coordinate `1`; the explicit
one-unit slack remains part of the supplied source-label adapter. -/
theorem aoyagiLemma5Eq3_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hlast : C.point ell ≤ L + 1)
    (hwidth :
      (n ((C.point 1 - 1) + 1) : ℤ) = aoyagiSelectedWidthNat ell m 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {k : ℕ} (hk : (k : ℤ) = aoyagiHtildeUpperNat ell a M m 1 + 1) :
    T (C.point 1 - 1) ∈ aoyagiHtildeIntervalValueSetNat ell a M m 1 ∧
      T (C.point 1 - 1) = (k : ℤ) - 1 ∧
        Sigma.mk (C.point 1 - 1) k ∈
          introducedLabelFinset L n (C.point 1 - 1) k := by
  have hown :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
      ell a M m C layerWidth T hell ha_lt hselected hsource hslack hT
  have hfinite :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
      L ell a n M m C layerWidth T hell ha_lt hselected hsource hslack hlast
      hwidth hT hk
  refine ⟨?_, hfinite.1, hfinite.2⟩
  have hp : 1 < ell + 1 := by omega
  rw [hown.2.1]
  exact aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
    ell a 1 M m hT.a_le_ell hp

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

/-- Inequality-shaped source-label bridge for equation `(5)`.

Actual label legality only needs the selected-width upper bound
`W_p<=n(S+1)`, not equality.  This is the source-facing form for an arbitrary
point in a selected block, where actual width may be larger than the selected
width. -/
theorem aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound
    (L ell a p alpha S : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hpell : p ≤ ell)
    (halpha_pos : 1 ≤ alpha)
    (halpha_le_excess : alpha ≤ aoyagiLemma5IntervalExcess ell a p)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hs_pos : 1 ≤ S) (hs_le : S ≤ L)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
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
      rw [hk]
      exact le_trans hlabel.2 hwidth_le
    exact_mod_cast hk_le_int

/-- Equation `(5)` strict-alpha-domain source-label bridge.

Membership in the strict alpha domain packages exactly the two label-arithmetic
guards used by `aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound`: `1<=alpha`
and `alpha<=Htilde'_p-Htilde_p`.  The additional strict guard `alpha<p`
remains visible in the domain but is not needed for label legality itself. -/
theorem aoyagiLemma5Eq5_alphaFamily_actualWidthLabel_at_of_widthBound
    (L ell a p alpha S : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hpell : p ≤ ell)
    (halpha : alpha ∈ aoyagiLemma5Eq5AlphaDomain ell a p)
    (hselected : (∑ j : Fin (ell + 1), m j) =
      (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hs_pos : 1 ≤ S) (hs_le : S ≤ L)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    {k : ℕ} (hk :
      (k : ℤ) = aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    actualWidthLabel L n S k := by
  rcases
    (aoyagiLemma5Eq5_alphaFamily_mem_iff_guards ell a p alpha).mp halpha with
    ⟨halpha_pos, halpha_le_excess, _halpha_lt_p⟩
  exact aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound
    L ell a p alpha S n M m hell ha hpell halpha_pos halpha_le_excess
    hselected hsource hs_pos hs_le hwidth_le hk

/-- The terminal selected coordinate `C.point ell - 1` is a positive source
index when the selected list has positive length.

This is source-index bookkeeping only. -/
theorem aoyagiLemma5_terminalSourceIndex_pos
    (ell : ℕ) (C : AoyagiSelectedCutpoints ell) (hell : 1 ≤ ell) :
    1 ≤ C.point ell - 1 := by
  have hpoint0 : 1 ≤ C.point 0 := C.point_pos_of_lt (by omega)
  have hstrict : C.point 0 < C.point ell :=
    C.point_strict_of_lt (by omega) (by omega)
  omega

/-- The terminal label `k=1` is an actual source label at the terminal selected
coordinate under explicit source-range and width-positivity hypotheses.

This proves only label legality.  It does not construct a terminal source
branch or prove terminal-minimum-label exactness. -/
theorem aoyagiLemma5_terminal_actualWidthLabel_of_lastPoint
    (L ell : ℕ) (n : ℕ → ℕ) (C : AoyagiSelectedCutpoints ell)
    (hell : 1 ≤ ell) (hlast : C.point ell ≤ L + 1)
    (hwidth_pos : 1 ≤ n (C.point ell)) :
    actualWidthLabel L n (C.point ell - 1) 1 := by
  have hpoint_pos : 1 ≤ C.point ell := C.point_pos_of_lt (by omega)
  have hsucc : C.point ell - 1 + 1 = C.point ell := by
    omega
  refine ⟨?_, ?_, by omega, ?_⟩
  · exact aoyagiLemma5_terminalSourceIndex_pos ell C hell
  · omega
  · change 1 ≤ n (C.point ell - 1 + 1)
    rw [hsucc]
    exact hwidth_pos

/-- A supplied terminal source-coordinate zero gives terminal interval
membership and introduced-label membership for the terminal label `k=1`.

The equality `T(C.point ell - 1)=0` is supplied.  This theorem does not
construct the terminal source branch or any classifier data. -/
theorem aoyagiLemma5_terminal_intervalValue_mem_introducedLabelFinset_of_terminalZero
    (L ell a : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hlast : C.point ell ≤ L + 1)
    (hwidth_pos : 1 ≤ n (C.point ell))
    (hterminal : T (C.point ell - 1) = 0) :
    T (C.point ell - 1) ∈
        aoyagiHtildeIntervalValueSetNat ell a M m ell ∧
      T (C.point ell - 1) = (1 : ℤ) - 1 ∧
        Sigma.mk (C.point ell - 1) 1 ∈
          introducedLabelFinset L n (C.point ell - 1) 1 := by
  have hlabel :
      actualWidthLabel L n (C.point ell - 1) 1 :=
    aoyagiLemma5_terminal_actualWidthLabel_of_lastPoint
      L ell n C hell hlast hwidth_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [hterminal,
      aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum
        ell a M m ha hselected]
    simp
  · rw [hterminal]
    norm_num
  · exact mem_introducedLabelFinset.mpr
      (introducedLabel_of_eq_stage_le hlabel rfl le_rfl)

/-- Equation `(5)`'s source guards put every member of the own selected block
in the positive source-layer range.

This is only lower-bound bookkeeping for source indices.  It uses
`1<=alpha<p` and the strict positivity/monotonicity of selected cutpoints. -/
theorem aoyagiLemma5Eq5_sourceIndex_pos_of_ownBlock
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S : ℕ} (hS : C.block p S) :
    1 ≤ S := by
  have halpha_pos : 1 ≤ alpha := hT.alpha_pos
  have halpha_lt_p : alpha < p := hT.alpha_lt_p
  have hp_pos : 0 < p := by omega
  have hp_lt_ell : p < ell := hS.1
  have hpoint0_pos : 1 ≤ C.point 0 := C.point_pos_of_lt (by omega)
  have hpoint_strict : C.point 0 < C.point p :=
    C.point_strict_of_lt hp_pos (by omega)
  have hpoint_p_ge_two : 2 ≤ C.point p := by omega
  exact le_trans (by omega) hS.2.1

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

/-- Inequality-shaped arbitrary-own-block version of equation `(5)` source
label legality.

For any `S` in the own selected block `C.block p S`, a supplied piecewise
certificate gives `T S=k-1`.  The actual-label conclusion only needs
`W_p<=n(S+1)`, not equality. -/
theorem aoyagiLemma5Eq5_piecewise_block_actualWidthLabel_of_widthBound
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
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  have hown :=
    aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
      ell a p alpha M m C layerWidth T hT
  constructor
  · exact aoyagiLemma5Eq5_ownCoordinate_eq_label_pred
      ell a p alpha M m C T hown hS hk
  · exact aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound
      L ell a p alpha S n M m hell hT.a_le_ell (le_of_lt hS.1)
      hT.alpha_pos hT.alpha_le_excess hselected hsource hs_pos hs_le
      hwidth_le hk

/-- Source-shaped arbitrary-own-block version of equation `(5)` label
legality.

Compared with
`aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_block`, this
wrapper derives the lower source-layer range condition `1<=S` from the Eq. `(5)`
guards and selected-block membership.  The upper range `S<=L` and the actual
width compatibility at `S` remain explicit. -/
theorem aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_ownBlock_widthCompatibility
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hs_le : S ≤ L)
    (hwidth : (n (S + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  exact aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_block
    L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS
    (aoyagiLemma5Eq5_sourceIndex_pos_of_ownBlock ell a p alpha M m C layerWidth T hT hS)
    hs_le hwidth hk

/-- Source-shaped arbitrary-own-block equation `(5)` label legality with
width bound instead of width equality.

This derives the lower source-layer bound from Eq. `(5)`'s own-block guards.
The upper range `S<=L` and the actual-width lower bound `W_p<=n(S+1)` remain
explicit. -/
theorem aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hs_le : S ≤ L)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  exact aoyagiLemma5Eq5_piecewise_block_actualWidthLabel_of_widthBound
    L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS
    (aoyagiLemma5Eq5_sourceIndex_pos_of_ownBlock ell a p alpha M m C layerWidth T hT hS)
    hs_le hwidth_le hk

/-- Source-shaped arbitrary-own-block equation `(5)` label legality from the
last selected cutpoint range.

Compared with
`aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_ownBlock_widthCompatibility`,
this wrapper derives both source-layer range conditions for `S`: the lower
bound from Eq. `(5)`'s own-block guards, and the upper bound from the source
compatibility `S_(ell+1)<=L+1`.  The actual-width compatibility at the
particular `S` remains explicit. -/
theorem aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthCompatibility
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth : (n (S + 1) : ℤ) = aoyagiSelectedWidthNat ell m p)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  exact aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_ownBlock_widthCompatibility
    L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS
    (C.block_sourceIndex_le_of_lastPoint_le hS hlast) hwidth hk

/-- Source-shaped arbitrary-own-block equation `(5)` label legality from the
last selected cutpoint range, with width bound instead of width equality.

This derives both source-layer range conditions for `S` while keeping the
actual-width lower bound at `S` explicit. -/
theorem aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  exact aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_widthBound
    L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS
    (C.block_sourceIndex_le_of_lastPoint_le hS hlast) hwidth_le hk

/-- Source-shaped equation `(5)` own-block wrapper with interval membership
and post-advance introduced-label membership.

The state is `(S,k)`: the supplied branch gives `T S=k-1`, while the actual
label is introduced after advancing the current layer through label `k`.  This
remains conditional on the supplied piecewise certificate and the explicit
actual-width lower bound. -/
theorem aoyagiLemma5Eq5_piecewise_ownBlock_intervalValue_introducedLabel_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S ∈ aoyagiHtildeIntervalValueSetNat ell a M m p ∧
      T S = (k : ℤ) - 1 ∧ introducedLabel L n S k S k := by
  have hown :=
    aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
      ell a p alpha M m C layerWidth T hT
  have hlabel :=
    aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS
      hlast hwidth_le hk
  refine ⟨?_, hlabel.1, ?_⟩
  · exact aoyagiLemma5Eq5_ownCoordinate_mem_intervalValueSetNat
      ell a p alpha M m C T hown hS
  · exact introducedLabel_of_eq_stage_le hlabel.2 rfl le_rfl

/-- Finite-domain version of
`aoyagiLemma5Eq5_piecewise_ownBlock_intervalValue_introducedLabel_of_lastPoint_widthBound`. -/
theorem aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S ∈ aoyagiHtildeIntervalValueSetNat ell a M m p ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  have h :=
    aoyagiLemma5Eq5_piecewise_ownBlock_intervalValue_introducedLabel_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
      hwidth_le hk
  exact ⟨h.1, h.2.1, mem_introducedLabelFinset.mpr h.2.2⟩

/-- Equation `(5)` own-block wrapper with strict-offset membership and
finite-domain introduced-label membership.

This is still for one supplied `alpha` and one supplied piecewise certificate;
it does not package all offsets at once. -/
theorem aoyagiLemma5Eq5_ownBlock_offsetValue_mem_introducedLabelFinset_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S ∈ aoyagiLemma5Eq5OffsetValueSet ell a p M m ∧
      T S ∈ aoyagiHtildeIntervalValueSetNat ell a M m p ∧
        T S = (k : ℤ) - 1 ∧
          Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  have hown :=
    aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
      ell a p alpha M m C layerWidth T hT
  have hfinite :=
    aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
      hwidth_le hk
  exact ⟨aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet
    ell a p alpha M m C T hown hS, hfinite⟩

/-- In the rising region, a supplied Eq5 strict-offset branch lands in the
same-coordinate interval with both endpoints erased, while retaining its
finite-domain introduced-label membership.

This is a one-branch adapter from the Eq5 strict-offset finite-domain theorem
through the finite-set equality
`aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min`.  It does not
package all offsets, construct displayed vectors, or prove an order count. -/
theorem
    aoyagiLemma5Eq5_ownBlock_eraseEndpoints_mem_introducedLabelFinset_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S ∈ ((aoyagiHtildeIntervalValueSetNat ell a M m p).erase
        (aoyagiHtildeUpperNat ell a M m p)).erase
          (aoyagiHtildeLowerNat ell a M m p) ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  have hoffset :=
    aoyagiLemma5Eq5_ownBlock_offsetValue_mem_introducedLabelFinset_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
      hwidth_le hk
  have hinterior_eq :=
    aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min
      ell a p M m hT.a_le_ell hp_pos hp_a hp_c
  refine ⟨?_, hoffset.2.2.1, hoffset.2.2.2⟩
  rw [← hinterior_eq]
  exact hoffset.1

/-- A supplied Eq5 own-block branch gives the one-step finite-domain update
for its current-layer label.

This specializes `introducedLabelFinset_succ_eq_insert` to the Eq5 label
`J+1 = Htilde'_p+1-alpha`, using only the supplied actual-width lower bound at
the own-block source index.  It is finite-domain bookkeeping, not an exponent
certificate or displayed-vector construction. -/
theorem aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_succ_eq_insert_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S J : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    introducedLabelFinset L n S (J + 1) =
      insert (Sigma.mk S (J + 1)) (introducedLabelFinset L n S J) := by
  have hlabel :=
    aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
      hwidth_le hJ
  exact introducedLabelFinset_succ_eq_insert hlabel.2

/-- A supplied Eq5 own-block branch increases the introduced-label finite-domain
cardinality by one when advancing through its current-layer label.

This is the cardinality form of
`aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_succ_eq_insert_of_lastPoint_widthBound`.
It remains finite-domain bookkeeping, not a displayed-vector construction,
order count, or exponent certificate. -/
theorem aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_card_succ_eq_succ_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S J : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    (introducedLabelFinset L n S (J + 1)).card =
      (introducedLabelFinset L n S J).card + 1 := by
  have hlabel :=
    aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
      hwidth_le hJ
  exact introducedLabelFinset_card_succ_eq_succ hlabel.2

/-- Source-facing Eq5 specialization of the supplied Case 2 recurrence-weight
update.

For one supplied Eq5 own-block branch whose label is `J+1`, a supplied
successor recurrence state with the standard Case 2 post-data has row weights
multiplied by the new variable from row `J+1` onward.  This is conditional
recurrence bookkeeping and does not assert that a blow-up chart produces the
post-state. -/
theorem aoyagiLemma5Eq5_ownBlock_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_widthBound
    {α : Type*} [CommMonoid α]
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S J : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    {pre : IntroducedLabelRecurrenceState L n S J α}
    {post : IntroducedLabelRecurrenceState L n S (J + 1) α}
    {u : α}
    (hpost : IntroducedLabelRecurrenceState.Case2SuppliedPostData pre post u) :
    ∀ i, J + 1 ≤ i → post.weight i = u * pre.weight i := by
  have hlabel :=
    aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
      hwidth_le hJ
  exact fun i hi ↦ hpost.weight_succ_current_eq_new_mul_of_ge hlabel.2 hi

/-- Source-facing Eq5 supplied exponent-domain extension.

For one supplied Eq5 own-block branch whose label is `J+1`, the existing
source-label wrapper supplies the new label's introduced-label field.  The
terminal exponent and least-value fields are supplied explicitly; this theorem
only routes them through the generic one-step exponent-certificate domain
extension. -/
theorem aoyagiLemma5Eq5_ownBlock_extendExponentDomain_succ_current_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S J : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hJ : ((J + 1 : ℕ) : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    (hcert : IntroducedLabelExponentCertificates L n S J t numerator leastValue)
    (hterminal :
      terminalExponent L (widthZ n) (t' S (J + 1)) =
        numerator' S (J + 1))
    (hleast :
      IsLeast
        {v : ℤ | ∃ i, i ∈ Finset.Icc 1 L ∧ t' S (J + 1) i = v}
        (leastValue' S (J + 1)))
    (ht_old : ∀ {s k}, introducedLabel L n S J s k → t' s k = t s k)
    (hn_old : ∀ {s k}, introducedLabel L n S J s k →
      numerator' s k = numerator s k)
    (hl_old : ∀ {s k}, introducedLabel L n S J s k →
      leastValue' s k = leastValue s k) :
    IntroducedLabelExponentCertificates L n S (J + 1) t' numerator' leastValue' := by
  have hlabel :=
    aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
      hwidth_le hJ
  have hnew :
      LabelExponentCertificate L n S (J + 1) S (J + 1)
        (t' S (J + 1)) (numerator' S (J + 1)) (leastValue' S (J + 1)) := by
    refine
      { introduced := ?_
        terminalExponent_eq := hterminal
        least_value := hleast }
    exact introducedLabel_of_eq_stage_le hlabel.2 rfl le_rfl
  exact hcert.extendDomain_succ_current hnew ht_old hn_old hl_old

/-- Source-shaped arbitrary-own-block equation `(5)` label legality from a
block-local actual-width lower-bound hypothesis.

The hypothesis `hactual` says that throughout each selected block, the
corresponding selected width is bounded by the actual width.  This is the
direct bridge needed by the width-bound wrapper; it is intentionally explicit
and does not claim to follow from Definition 3 alone. -/
theorem aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_blockWidth
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hactual :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          aoyagiSelectedWidthNat ell m i.val ≤ (n r : ℤ))
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  exact aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
    L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
    (C.selectedWidthNat_le_actualWidth_of_block n m hactual hS) hk

/-- Source-shaped arbitrary-own-block equation `(5)` label legality from
selected left-endpoint widths and a block-local minimum condition. -/
theorem aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_leftMin
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hleft :
      ∀ i : Fin ell,
        (n (C.point i.val) : ℤ) = aoyagiSelectedWidthNat ell m i.val)
    (hmin :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          n (C.point i.val) ≤ n r)
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  exact aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
    L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
    (C.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min
      n m hleft hmin hS)
    hk

/-- Source-shaped arbitrary-own-block equation `(5)` label legality from
selected-cutpoint actual widths and off-selected-layer dominance.

This removes the explicit width-bound argument from
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound`,
replacing it by two source-facing data hypotheses: selected cutpoints have
widths `m`, and every off-selected layer is at least as wide as every selected
width.  These hypotheses are explicit because Definition 3's set-valued
selection language should not be read as a no-duplicate layer-position
statement. -/
theorem aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hselectedWidth : ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i ≤ (n t : ℤ))
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  exact aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
    L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS hlast
    (C.selectedWidthNat_le_actualWidth_of_block_of_offSelected
      n m hS hselectedWidth hoffSelected)
    hk

/-- Strict off-selected-layer dominance version of
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected`. -/
theorem aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected_lt
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (C : AoyagiSelectedCutpoints ell)
    (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hselectedWidth : ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i < (n t : ℤ))
    {S k : ℕ} (hS : C.block p S) (hlast : C.point ell ≤ L + 1)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 ∧ actualWidthLabel L n S k := by
  exact aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected
    L ell a p alpha n M m C layerWidth T hell hselected hsource hT
    hselectedWidth
    (fun t ht i ↦ le_of_lt (hoffSelected t ht i))
    hS hlast hk

end Aoyagi
end DLN
end DLNFibre
