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

namespace AoyagiDefinition3CeilData

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

end Aoyagi
end DLN
end DLNFibre
