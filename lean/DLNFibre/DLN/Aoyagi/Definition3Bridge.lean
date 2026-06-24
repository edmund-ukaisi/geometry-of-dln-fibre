import DLNFibre.DLN.Aoyagi.FinalFormula

/-!
# Bridges from Aoyagi Definition 3 data to existing finite arithmetic

This file consumes the supplied ceiling datum from Aoyagi Definition 3 and
feeds it into the existing Lemma 4 and `Htilde` arithmetic APIs.  It proves
only finite consequences of the selected-sum identity.  It does not prove the
Definition 3 selection inequalities, vector admissibility, pole order, normal
crossings, or RLCT extraction.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Definition 3's source-shaped selected-cutpoint data.

The selected cutpoints themselves are supplied.  This structure records the
displayed selected and nonselected inequalities from Aoyagi Definition 3. -/
structure AoyagiDefinition3SourceData
    (L ell : ℕ) (H : ℕ → ℕ) (r : ℕ)
    (C : AoyagiSelectedCutpoints ell) : Prop where
  ell_pos : 0 < ell
  cut_le : ∀ j : Fin (ell + 1), C.cut j ≤ L + 1
  selected_strict :
    ∀ i : Fin (ell + 1),
      (ell : ℤ) * aoyagiReducedWidthInt H r (C.cut i) <
        ∑ j : Fin (ell + 1), aoyagiReducedWidthInt H r (C.cut j)
  selected_lt_nonselected :
    ∀ i : Fin (ell + 1), ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
      aoyagiReducedWidthInt H r s ∉
        Finset.univ.image (fun j : Fin (ell + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) →
        aoyagiReducedWidthInt H r (C.cut i) < aoyagiReducedWidthInt H r s
  nonselected_le :
    ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
      aoyagiReducedWidthInt H r s ∉
        Finset.univ.image (fun j : Fin (ell + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) →
        ∑ j : Fin (ell + 1), aoyagiReducedWidthInt H r (C.cut j) ≤
          ((ell : ℤ) - 1) * aoyagiReducedWidthInt H r s

/-- Definition 3's strict selected inequality and nonselected upper inequality
force selected widths to be strictly smaller than a nonselected width, provided
the selected width is nonnegative. -/
theorem aoyagiDefinition3_selected_lt_of_selectedStrict_nonselectedLe
    {ell : ℕ} {selected width total : ℤ}
    (hell : 0 < ell)
    (hselected_nonneg : 0 ≤ selected)
    (hstrict : (ell : ℤ) * selected < total)
    (hnonselected : total ≤ ((ell : ℤ) - 1) * width) :
    selected < width := by
  have hchain : (ell : ℤ) * selected < ((ell : ℤ) - 1) * width :=
    lt_of_lt_of_le hstrict hnonselected
  by_contra hnot
  have hwidth_le : width ≤ selected := le_of_not_gt hnot
  have hcoef_nonneg : 0 ≤ ((ell : ℤ) - 1) := by
    omega
  have hprod_le :
      ((ell : ℤ) - 1) * width ≤ ((ell : ℤ) - 1) * selected :=
    mul_le_mul_of_nonneg_left hwidth_le hcoef_nonneg
  have hbad : (ell : ℤ) * selected < ((ell : ℤ) - 1) * selected :=
    lt_of_lt_of_le hchain hprod_le
  have hsplit :
      (ell : ℤ) * selected = ((ell : ℤ) - 1) * selected + selected := by
    ring
  rw [hsplit] at hbad
  omega

namespace AoyagiDefinition3CeilData

/-- A positive `ell` determines Definition 3's ceiling/residue datum for any
integer selected-width family. -/
theorem nonempty_of_ell_pos
    (ell : ℕ) (m : Fin (ell + 1) → ℤ) (hell : 0 < ell) :
    Nonempty (AoyagiDefinition3CeilData ell m) := by
  classical
  let T : ℤ := ∑ j : Fin (ell + 1), m j
  let e : ℤ := ell
  have hepos : 0 < e := by
    simpa [e] using (show (0 : ℤ) < (ell : ℤ) by exact_mod_cast hell)
  have hene : e ≠ 0 := ne_of_gt hepos
  by_cases hmod : T % e = 0
  · refine ⟨{
      ell_pos := hell
      ceilWidth := T / e
      aParam := ell
      selectedSum_eq := ?_
      aParam_pos := hell
      aParam_le := le_rfl }⟩
    have hT : e * (T / e) = T := by
      have h := Int.emod_add_mul_ediv T e
      rw [hmod, zero_add] at h
      simpa [mul_comm] using h
    calc
      T = e * (T / e) := hT.symm
      _ = (ell : ℤ) * (T / e - 1) + ell := by
        simp [e]
        ring
  · let a : ℕ := (T % e).toNat
    have hmod_nonneg : 0 ≤ T % e := Int.emod_nonneg T hene
    have hmod_pos : 0 < T % e := by omega
    have hmod_lt : T % e < e := Int.emod_lt_of_pos T hepos
    have hcast_a : (a : ℤ) = T % e := by
      dsimp [a]
      exact Int.toNat_of_nonneg hmod_nonneg
    have hapos : 0 < a := by
      have hapos_int : (0 : ℤ) < (a : ℤ) := by
        simpa [hcast_a] using hmod_pos
      exact_mod_cast hapos_int
    have hale : a ≤ ell := by
      have hle_int : (a : ℤ) ≤ (ell : ℤ) := by
        have hle : T % e ≤ e := le_of_lt hmod_lt
        simpa [hcast_a, e] using hle
      exact_mod_cast hle_int
    refine ⟨{
      ell_pos := hell
      ceilWidth := T / e + 1
      aParam := a
      selectedSum_eq := ?_
      aParam_pos := hapos
      aParam_le := hale }⟩
    calc
      T = T % e + e * (T / e) := (Int.emod_add_mul_ediv T e).symm
      _ = (ell : ℤ) * (T / e + 1 - 1) + a := by
        rw [hcast_a]
        simp [e]
        ring

/-- Definition 3's ceiling datum has a positive selected-count parameter. -/
theorem one_le_ell {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    1 ≤ ell :=
  data.ell_pos

/-- Definition 3's residue parameter satisfies `1 <= a`. -/
theorem one_le_aParam {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    1 ≤ data.aParam :=
  data.aParam_pos

/-- Definition 3's selected-sum identity makes the Lemma 4 terminal endpoint
vanish. -/
theorem terminalEndpoint_eq_zero {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiLemma4TerminalEndpoint ell data.aParam data.ceilWidth m = 0 :=
  aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum
    ell data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq

/-- Definition 3's selected-sum identity makes the lower displayed `Htilde`
chain vanish at the terminal selected coordinate. -/
theorem htildeLowerChain_last_eq_zero {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiHtildeLowerChain ell data.aParam data.ceilWidth m (Fin.last ell) = 0 :=
  aoyagiHtildeLowerChain_last_eq_zero_of_selectedSum
    ell data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq

/-- Definition 3's selected-sum identity makes the upper displayed `Htilde'`
chain vanish at the terminal selected coordinate. -/
theorem htildeUpperChain_last_eq_zero {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiHtildeUpperChain ell data.aParam data.ceilWidth m (Fin.last ell) = 0 :=
  aoyagiHtildeUpperChain_last_eq_zero_of_selectedSum
    ell data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq

/-- Nat-indexed form of the lower displayed chain's terminal zero. -/
theorem htildeLowerNat_last_eq_zero {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiHtildeLowerNat ell data.aParam data.ceilWidth m ell = 0 :=
  aoyagiHtildeLowerNat_last_eq_zero_of_selectedSum
    ell data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq

/-- Nat-indexed form of the upper displayed chain's terminal zero. -/
theorem htildeUpperNat_last_eq_zero {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiHtildeUpperNat ell data.aParam data.ceilWidth m ell = 0 :=
  aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum
    ell data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq

/-- The penultimate upper-chain endpoint rewrite supplied by Definition 3's
selected-sum identity. -/
theorem htildeUpperNat_pred_eq_sub_lastWidth {ell : ℕ}
    {m : Fin (ell + 1) → ℤ} (data : AoyagiDefinition3CeilData ell m) :
    aoyagiHtildeUpperNat ell data.aParam data.ceilWidth m (ell - 1) =
      data.ceilWidth - aoyagiSelectedWidthNat ell m ell :=
  aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum
    ell data.aParam data.ceilWidth m data.aParam_pos data.aParam_le
    data.selectedSum_eq

/-- If a chain is squeezed between the lower and upper displayed `Htilde`
chains, then its terminal value is zero under Definition 3's selected-sum
datum. -/
theorem Hlast_eq_zero_of_htildeChainBounds {ell : ℕ}
    {m H : Fin (ell + 1) → ℤ} (data : AoyagiDefinition3CeilData ell m)
    (hlower : aoyagiHtildeLowerChain ell data.aParam data.ceilWidth m ≤ H)
    (hupper : H ≤ aoyagiHtildeUpperChain ell data.aParam data.ceilWidth m) :
    H (Fin.last ell) = 0 := by
  have hlo0 := data.htildeLowerChain_last_eq_zero
  have hhi0 := data.htildeUpperChain_last_eq_zero
  have hlo := hlower (Fin.last ell)
  have hhi := hupper (Fin.last ell)
  rw [hlo0] at hlo
  rw [hhi0] at hhi
  exact le_antisymm hhi hlo

/-- The finite interval-size excess sum has the same arithmetic value as
Aoyagi Theorem 2's displayed order formula.

This is only the elementary count formula.  It does not identify this number
with a pole order. -/
theorem intervalSize_excess_sum_Icc_eq_theorem2OrderFormula
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    1 + (∑ j ∈ Finset.Icc 1 (ell - 1),
        (aoyagiLemma5IntervalSize ell data.aParam j - 1)) =
      data.theorem2OrderFormula := by
  have h :=
    aoyagiLemma5IntervalSize_excess_sum_Icc
      ell data.aParam data.one_le_ell data.aParam_le
  simpa [theorem2OrderFormula] using h

/-- The existing same-coordinate `Htilde` interval value-set count has the
same arithmetic value as Aoyagi Theorem 2's displayed order formula.

This is only finite value-set cardinality bookkeeping.  It does not prove
chart-family admissibility, no-extra terminal minima, or pole order. -/
theorem htildeIntervalValueSetNat_excess_sum_Icc_eq_theorem2OrderFormula
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    1 + (∑ j ∈ Finset.Icc 1 (ell - 1),
        ((aoyagiHtildeIntervalValueSetNat
          ell data.aParam data.ceilWidth m j).card - 1)) =
      data.theorem2OrderFormula := by
  have h :=
    aoyagiHtildeIntervalValueSetNat_excess_sum_Icc
      ell data.aParam data.ceilWidth m data.one_le_ell data.aParam_le
  simpa [theorem2OrderFormula] using h

/-- The terminal same-coordinate `Htilde` interval is the singleton `{0}`
under Definition 3's selected-sum datum. -/
theorem htildeIntervalValueSetNat_terminal_eq_singleton_zero
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) :
    aoyagiHtildeIntervalValueSetNat ell data.aParam data.ceilWidth m ell = {0} :=
  aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum
    ell data.aParam data.ceilWidth m data.aParam_le data.selectedSum_eq

/-- A separately supplied terminal zero fills the terminal Eq5 finite set under
Definition 3's selected-sum datum. -/
theorem suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (hterminal : T (C.point ell - 1) = 0) :
    insert (T (C.point ell - 1))
        (aoyagiLemma5Eq5OffsetValueSet ell data.aParam ell data.ceilWidth m) =
      aoyagiHtildeIntervalValueSetNat ell data.aParam data.ceilWidth m ell :=
  aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat
    ell data.aParam data.ceilWidth m C T data.aParam_le data.selectedSum_eq
    hterminal

/-- Lemma 4's two-value count under supplied `Htilde` chain bounds and a
supplied two-value increment hypothesis. -/
theorem lemma4_twoValueCount_of_htildeChainBounds
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) (H : Fin (ell + 1) → ℤ)
    (hH0 : H 0 = m 0)
    (hlower : aoyagiHtildeLowerChain ell data.aParam data.ceilWidth m ≤ H)
    (hupper : H ≤ aoyagiHtildeUpperChain ell data.aParam data.ceilWidth m)
    (hvals : ∀ j : Fin ell,
      aoyagiLemma4F ell m H j = data.ceilWidth - 1 ∨
        aoyagiLemma4F ell m H j = data.ceilWidth) :
    ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m H j = data.ceilWidth).card = data.aParam) ∧
      ((Finset.univ.filter fun j : Fin ell ↦
        aoyagiLemma4F ell m H j = data.ceilWidth - 1).card =
          ell - data.aParam) :=
  aoyagiLemma4_twoValueCount_of_HtildeChainBounds
    ell data.aParam data.ceilWidth m H hH0 data.aParam_le data.selectedSum_eq
    hlower hupper hvals

/-- Definition 3's strict selected-width inequalities, when supplied
separately, bound every selected width by `ceilWidth-1`. -/
theorem selectedWidth_le_pred_of_sourceSelectedInequality
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (i : Fin (ell + 1)) :
    m i ≤ data.ceilWidth - 1 :=
  aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
    ell data.aParam data.ceilWidth m data.ell_pos data.aParam_le
    data.selectedSum_eq hsource i

/-- Source-selected inequalities plus Definition 3 data and supplied index
guards give equation `(4)`'s lower-chain label bounds, with the source
inequalities still explicit. -/
theorem htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) {p : ℕ}
    (hp0 : 1 ≤ p) (hp_a : p ≤ data.aParam)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    1 ≤ aoyagiHtildeLowerNat ell data.aParam data.ceilWidth m p + 1 ∧
      aoyagiHtildeLowerNat ell data.aParam data.ceilWidth m p + 1 ≤
        aoyagiSelectedWidthNat ell m p :=
  aoyagiHtildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
    ell data.aParam p data.ceilWidth m data.ell_pos data.aParam_le hp0 hp_a
    data.selectedSum_eq hsource

/-- Source-selected inequalities plus Definition 3 data and supplied index
guards give equation `(4)`'s local finite arithmetic package, with the
displayed-vector construction still outside this theorem. -/
theorem lemma5Eq4_localData_of_sourceSelectedInequality
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) {p : ℕ}
    (hp0 : 1 ≤ p) (hp_tail : p + 1 ≤ data.aParam)
    (hp_c : p ≤ ell - data.aParam)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    p + (ell - data.aParam) + 2 ≤ ell + 1 ∧
      aoyagiHtildeUpperNat ell data.aParam data.ceilWidth m p - (p : ℤ) =
        aoyagiHtildeLowerNat ell data.aParam data.ceilWidth m p ∧
      (1 ≤ aoyagiHtildeLowerNat ell data.aParam data.ceilWidth m p + 1 ∧
        aoyagiHtildeLowerNat ell data.aParam data.ceilWidth m p + 1 ≤
          aoyagiSelectedWidthNat ell m p) :=
  aoyagiLemma5Eq4_localData_of_sourceSelectedInequality
    ell data.aParam p data.ceilWidth m data.ell_pos data.aParam_le hp0 hp_tail
    hp_c data.selectedSum_eq hsource

/-- Source-selected inequalities plus Definition 3 data and supplied
index/alpha guards give equation `(5)`'s displayed label bounds, with source
inequalities still explicit. -/
theorem lemma5Eq5_labelBounds_of_sourceSelectedInequality
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) {p alpha : ℕ}
    (hpell : p ≤ ell) (halpha_pos : 1 ≤ alpha)
    (halpha_le_excess : alpha ≤ aoyagiLemma5IntervalExcess ell data.aParam p)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    1 ≤ aoyagiHtildeUpperNat ell data.aParam data.ceilWidth m p + 1 -
        (alpha : ℤ) ∧
      aoyagiHtildeUpperNat ell data.aParam data.ceilWidth m p + 1 -
          (alpha : ℤ) ≤
        aoyagiSelectedWidthNat ell m p :=
  aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality
    ell data.aParam p alpha data.ceilWidth m data.ell_pos data.aParam_le hpell
    halpha_pos halpha_le_excess data.selectedSum_eq hsource

/-- Source-selected inequalities plus Definition 3 data and supplied
interior/slack guards give equation `(3)`'s local finite arithmetic package. -/
theorem lemma5Eq3_localData_of_sourceSelectedInequality_and_slack
    {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (ha_lt : data.aParam < ell)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ data.ceilWidth) :
    (ell - data.aParam) + 2 ≤ ell + 1 ∧
      aoyagiHtildeUpperNat ell data.aParam data.ceilWidth m 1 -
      aoyagiHtildeLowerNat ell data.aParam data.ceilWidth m 1 =
        1 ∧
      (1 ≤ aoyagiHtildeUpperNat ell data.aParam data.ceilWidth m 1 + 1 ∧
        aoyagiHtildeUpperNat ell data.aParam data.ceilWidth m 1 + 1 ≤
          aoyagiSelectedWidthNat ell m 1) :=
  aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack
    ell data.aParam data.ceilWidth m data.one_le_ell data.aParam_le
    data.one_le_aParam ha_lt data.selectedSum_eq hsource hslack

end AoyagiDefinition3CeilData

namespace AoyagiDefinition3SourceData

/-- Constructor for Definition 3 source data when the strict selected
inequality, nonselected upper inequality, and source-range rank-width
hypothesis are supplied.

The `selected_lt_nonselected` field is derived by elementary integer
arithmetic; selected cutpoints and the remaining Definition 3 inequalities
remain supplied. -/
theorem of_selectedStrict_nonselectedLe_rankWidth
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (hell : 0 < ell)
    (hcut_le : ∀ j : Fin (ell + 1), C.cut j ≤ L + 1)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    (hselected_strict :
      ∀ i : Fin (ell + 1),
        (ell : ℤ) * aoyagiReducedWidthInt H r (C.cut i) <
          ∑ j : Fin (ell + 1), aoyagiReducedWidthInt H r (C.cut j))
    (hnonselected_le :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        aoyagiReducedWidthInt H r s ∉
          Finset.univ.image
            (fun j : Fin (ell + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) →
        ∑ j : Fin (ell + 1), aoyagiReducedWidthInt H r (C.cut j) ≤
          ((ell : ℤ) - 1) * aoyagiReducedWidthInt H r s) :
    AoyagiDefinition3SourceData L ell H r C where
  ell_pos := hell
  cut_le := hcut_le
  selected_strict := hselected_strict
  selected_lt_nonselected := by
    intro i s hs1 hsL hnot
    exact
      aoyagiDefinition3_selected_lt_of_selectedStrict_nonselectedLe
        hell
        (aoyagiReducedWidthInt_nonneg_of_rank_le H
          (hr (C.cut i) (C.pos i) (hcut_le i)))
        (hselected_strict i)
        (hnonselected_le s hs1 hsL hnot)
  nonselected_le := hnonselected_le

/-- The strict selected-width inequality from Definition 3, rewritten for the
selected reduced-width family used by the final formula layer. -/
theorem selected_strict_selectedReducedWidths
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C) :
    ∀ i : Fin (ell + 1),
      (ell : ℤ) * aoyagiSelectedReducedWidths H r C i <
        ∑ j : Fin (ell + 1), aoyagiSelectedReducedWidths H r C j := by
  simpa [aoyagiSelectedReducedWidths] using S.selected_strict

/-- The strict selected-width inequality from Definition 3, rewritten along a
supplied equality identifying an arbitrary selected-width family with Aoyagi's
selected reduced widths. -/
theorem selected_strict_of_eq_selectedReducedWidths
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (hm : m = aoyagiSelectedReducedWidths H r C) :
    ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j := by
  subst hm
  exact S.selected_strict_selectedReducedWidths

/-- The last selected cutpoint lies in the source range, as recorded by
Definition 3 source data. -/
theorem lastPoint_le
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C) :
    C.point ell ≤ L + 1 := by
  simpa [AoyagiSelectedCutpoints.point, Fin.last] using S.cut_le (Fin.last ell)

/-- Supplied Definition 3 source data determines the ceiling/residue datum and
retains the strict selected inequality for downstream arithmetic. -/
theorem exists_ceilData
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C) :
    ∃ _data : AoyagiDefinition3CeilData ell (aoyagiSelectedReducedWidths H r C),
      ∀ i : Fin (ell + 1),
        (ell : ℤ) * aoyagiSelectedReducedWidths H r C i <
          ∑ j : Fin (ell + 1), aoyagiSelectedReducedWidths H r C j := by
  rcases AoyagiDefinition3CeilData.nonempty_of_ell_pos
      ell (aoyagiSelectedReducedWidths H r C) S.ell_pos with ⟨data⟩
  exact ⟨data, S.selected_strict_selectedReducedWidths⟩

/-- Source data and a ceiling datum give Definition 3's selected-width upper
bound for the selected reduced widths.

This only consumes the strict selected inequality already stored in the source
data; it does not construct the selected cutpoints. -/
theorem selectedWidth_le_pred_of_ceilData
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (data :
      AoyagiDefinition3CeilData ell (aoyagiSelectedReducedWidths H r C))
    (i : Fin (ell + 1)) :
    aoyagiSelectedReducedWidths H r C i ≤ data.ceilWidth - 1 :=
  data.selectedWidth_le_pred_of_sourceSelectedInequality
    S.selected_strict_selectedReducedWidths i

/-- Source data plus Definition 3 ceiling data give equation `(4)`'s
lower-chain label bounds for the selected reduced widths, under the same
local index guards as the existing finite arithmetic theorem. -/
theorem htildeLowerNat_add_one_labelBounds_of_ceilData
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (data :
      AoyagiDefinition3CeilData ell (aoyagiSelectedReducedWidths H r C))
    {p : ℕ} (hp0 : 1 ≤ p) (hp_a : p ≤ data.aParam) :
    1 ≤ aoyagiHtildeLowerNat ell data.aParam data.ceilWidth
          (aoyagiSelectedReducedWidths H r C) p + 1 ∧
      aoyagiHtildeLowerNat ell data.aParam data.ceilWidth
          (aoyagiSelectedReducedWidths H r C) p + 1 ≤
        aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) p :=
  data.htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
    hp0 hp_a S.selected_strict_selectedReducedWidths

/-- Source data plus Definition 3 ceiling data give equation `(4)`'s local
finite arithmetic package for the selected reduced widths. -/
theorem lemma5Eq4_localData_of_ceilData
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (data :
      AoyagiDefinition3CeilData ell (aoyagiSelectedReducedWidths H r C))
    {p : ℕ}
    (hp0 : 1 ≤ p) (hp_tail : p + 1 ≤ data.aParam)
    (hp_c : p ≤ ell - data.aParam) :
    p + (ell - data.aParam) + 2 ≤ ell + 1 ∧
      aoyagiHtildeUpperNat ell data.aParam data.ceilWidth
          (aoyagiSelectedReducedWidths H r C) p - (p : ℤ) =
        aoyagiHtildeLowerNat ell data.aParam data.ceilWidth
          (aoyagiSelectedReducedWidths H r C) p ∧
      (1 ≤ aoyagiHtildeLowerNat ell data.aParam data.ceilWidth
            (aoyagiSelectedReducedWidths H r C) p + 1 ∧
        aoyagiHtildeLowerNat ell data.aParam data.ceilWidth
            (aoyagiSelectedReducedWidths H r C) p + 1 ≤
          aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) p) :=
  data.lemma5Eq4_localData_of_sourceSelectedInequality
    hp0 hp_tail hp_c S.selected_strict_selectedReducedWidths

/-- Source data plus Definition 3 ceiling data give equation `(5)`'s displayed
label bounds for the selected reduced widths. -/
theorem lemma5Eq5_labelBounds_of_ceilData
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (data :
      AoyagiDefinition3CeilData ell (aoyagiSelectedReducedWidths H r C))
    {p alpha : ℕ}
    (hpell : p ≤ ell) (halpha_pos : 1 ≤ alpha)
    (halpha_le_excess : alpha ≤
      aoyagiLemma5IntervalExcess ell data.aParam p) :
    1 ≤ aoyagiHtildeUpperNat ell data.aParam data.ceilWidth
          (aoyagiSelectedReducedWidths H r C) p + 1 - (alpha : ℤ) ∧
      aoyagiHtildeUpperNat ell data.aParam data.ceilWidth
            (aoyagiSelectedReducedWidths H r C) p + 1 - (alpha : ℤ) ≤
        aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) p :=
  data.lemma5Eq5_labelBounds_of_sourceSelectedInequality
    hpell halpha_pos halpha_le_excess S.selected_strict_selectedReducedWidths

/-- Source data plus Definition 3 ceiling data give equation `(3)`'s local
finite arithmetic package for the selected reduced widths, under the same
interior and slack hypotheses as the existing finite arithmetic theorem. -/
theorem lemma5Eq3_localData_of_ceilData_and_slack
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (data :
      AoyagiDefinition3CeilData ell (aoyagiSelectedReducedWidths H r C))
    (ha_lt : data.aParam < ell)
    (hslack :
      aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) 0 + 2 ≤
        data.ceilWidth) :
    (ell - data.aParam) + 2 ≤ ell + 1 ∧
      aoyagiHtildeUpperNat ell data.aParam data.ceilWidth
          (aoyagiSelectedReducedWidths H r C) 1 -
      aoyagiHtildeLowerNat ell data.aParam data.ceilWidth
          (aoyagiSelectedReducedWidths H r C) 1 =
        1 ∧
      (1 ≤ aoyagiHtildeUpperNat ell data.aParam data.ceilWidth
            (aoyagiSelectedReducedWidths H r C) 1 + 1 ∧
        aoyagiHtildeUpperNat ell data.aParam data.ceilWidth
            (aoyagiSelectedReducedWidths H r C) 1 + 1 ≤
          aoyagiSelectedWidthNat ell (aoyagiSelectedReducedWidths H r C) 1) :=
  data.lemma5Eq3_localData_of_sourceSelectedInequality_and_slack
    ha_lt S.selected_strict_selectedReducedWidths hslack

/-- Definition 3 source data plus a source-range rank-width hypothesis package
the selected reduced-width family, the resulting ceiling datum, Nat-width
rewrites, nonnegativity, the strict selected inequality, and the selected-width
upper bound.

The selected cutpoints and source data remain supplied.  The rank-width
hypothesis is explicit and pointwise on the source layer range. -/
theorem exists_selectedReducedWidthCeilData_of_rankWidth
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) := by
  rcases S.exists_ceilData with ⟨data, hsource⟩
  let m : Fin (ell + 1) → ℤ := aoyagiSelectedReducedWidths H r C
  have hrSelected : ∀ j : Fin (ell + 1), r ≤ H (C.cut j) :=
    fun j ↦ hr (C.cut j) (C.pos j) (S.cut_le j)
  refine ⟨m, data, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le H r C hrSelected j
  · intro j
    exact aoyagiSelectedReducedWidths_nonneg_of_rank_le H r C hrSelected j
  · exact hsource
  · intro i
    exact data.selectedWidth_le_pred_of_sourceSelectedInequality hsource i
  · intro i
    exact aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le
      H (r := r) (i := i) C hrSelected

end AoyagiDefinition3SourceData

end Aoyagi
end DLN
end DLNFibre
