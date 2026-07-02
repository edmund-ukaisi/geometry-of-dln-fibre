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
    Nonempty (AoyagiDefinition3CeilData ell m) :=
  ⟨AoyagiDefinition3CeilData.ofSelectedSumCeil ell m hell⟩

/-- Explicit Definition 3 ceiling datum from a positive-remainder
decomposition of the selected-width sum.

The integer `ceilPred` is the predecessor `ceilWidth - 1`; the source
ceiling integer is therefore `ceilPred + 1`. -/
def ofSelectedSumPositiveRemainder
    (ell : ℕ) (m : Fin (ell + 1) → ℤ) (ceilPred : ℤ) (a : ℕ)
    (hell : 0 < ell) (ha_pos : 0 < a) (ha_le : a ≤ ell)
    (hsum :
      (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * ceilPred + (a : ℤ)) :
    AoyagiDefinition3CeilData ell m where
  ell_pos := hell
  ceilWidth := ceilPred + 1
  aParam := a
  selectedSum_eq := by
    rw [hsum]
    ring
  aParam_pos := ha_pos
  aParam_le := ha_le

/-- Explicit Definition 3 ceiling datum for the equal-width selected family.

If the common selected width has positive-remainder decomposition
`w = L * q + a` with `0 < a <= L`, then Aoyagi's equal-width example has
`ceilWidth = w + q + 1` and `aParam = a`. -/
def equalWidthOfDecomposition
    (L w q a : ℕ) (ha_pos : 0 < a) (ha_le : a ≤ L)
    (hw : w = L * q + a) :
    AoyagiDefinition3CeilData L (fun _ : Fin (L + 1) ↦ (w : ℤ)) where
  ell_pos := lt_of_lt_of_le ha_pos ha_le
  ceilWidth := (w : ℤ) + (q : ℤ) + 1
  aParam := a
  selectedSum_eq := by
    have hwz : (w : ℤ) = (L : ℤ) * (q : ℤ) + (a : ℤ) := by
      exact_mod_cast hw
    calc
      (∑ _j : Fin (L + 1), (w : ℤ)) =
          ((L + 1 : ℕ) : ℤ) * (w : ℤ) := by
        simp [Finset.sum_const, Fintype.card_fin]
      _ = (L : ℤ) * (((w : ℤ) + (q : ℤ) + 1) - 1) + (a : ℤ) := by
        rw [hwz]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
  aParam_pos := ha_pos
  aParam_le := ha_le

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

/-- For `ell = 1`, Definition 3's residue parameter is forced to be `1`. -/
theorem aParam_eq_one_of_ell_eq_one {m : Fin (1 + 1) → ℤ}
    (data : AoyagiDefinition3CeilData 1 m) :
    data.aParam = 1 := by
  have hpos : 0 < data.aParam := data.aParam_pos
  have hle : data.aParam ≤ 1 := data.aParam_le
  omega

/-- For `ell = 1`, Definition 3's selected sum is exactly the ceiling
integer. -/
theorem selectedSum_eq_ceilWidth_of_ell_eq_one {m : Fin (1 + 1) → ℤ}
    (data : AoyagiDefinition3CeilData 1 m) :
    (∑ j : Fin (1 + 1), m j) = data.ceilWidth := by
  have ha := data.aParam_eq_one_of_ell_eq_one
  calc
    (∑ j : Fin (1 + 1), m j) =
        (1 : ℤ) * (data.ceilWidth - 1) + (1 : ℤ) := by
      simpa [ha] using data.selectedSum_eq
    _ = data.ceilWidth := by ring

/-- For `ell = 1`, the ceiling integer is the selected sum. -/
theorem ceilWidth_eq_selectedSum_of_ell_eq_one {m : Fin (1 + 1) → ℤ}
    (data : AoyagiDefinition3CeilData 1 m) :
    data.ceilWidth = ∑ j : Fin (1 + 1), m j :=
  data.selectedSum_eq_ceilWidth_of_ell_eq_one.symm

/-- For `ell = 1`, Definition 3's order formula is forced to be `1`. -/
theorem theorem2OrderFormula_eq_one_of_ell_eq_one {m : Fin (1 + 1) → ℤ}
    (data : AoyagiDefinition3CeilData 1 m) :
    data.theorem2OrderFormula = 1 := by
  simp [AoyagiDefinition3CeilData.theorem2OrderFormula,
    data.aParam_eq_one_of_ell_eq_one]

/-- For `ell = 1`, the Theorem 2 finite lambda formula is the regular term
plus half the selected pair sum, for every Definition 3 ceiling datum. -/
theorem theorem2Lambda_fromCeilData_eq_regularTerm_add_pairSum_half_of_ell_eq_one
    (L : ℕ) (H : ℕ → ℕ) (r : ℕ) {m : Fin (1 + 1) → ℤ}
    (data : AoyagiDefinition3CeilData 1 m) :
    aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
      aoyagiTheorem2RegularTerm L H r + aoyagiSelectedWidthPairSum 1 m / 2 := by
  have ha := data.aParam_eq_one_of_ell_eq_one
  unfold aoyagiTheorem2Lambda_fromCeilData aoyagiTheorem2Lambda_ceil
  rw [ha]
  ring

/-- For `ell = 1`, if the selected widths are `u` and `v`, the Theorem 2
finite lambda formula is `regularTerm + u*v/2`. -/
theorem theorem2Lambda_fromCeilData_eq_regularTerm_add_selectedPair_half_of_ell_eq_one
    (L : ℕ) (H : ℕ → ℕ) (r : ℕ) {m : Fin (1 + 1) → ℤ}
    (data : AoyagiDefinition3CeilData 1 m) {u v : ℕ}
    (hm0 : m (0 : Fin (1 + 1)) = (u : ℤ))
    (hm1 : m (1 : Fin (1 + 1)) = (v : ℤ)) :
    aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
      aoyagiTheorem2RegularTerm L H r + ((u : ℚ) * (v : ℚ)) / 2 := by
  rw [data.theorem2Lambda_fromCeilData_eq_regularTerm_add_pairSum_half_of_ell_eq_one]
  congr 1
  unfold aoyagiSelectedWidthPairSum
  simp [Fin.sum_univ_two, hm0, hm1]

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

/-- Equal-width source data for Aoyagi's Definition 3.

If every source-range reduced width is the same positive value `w`, Aoyagi's
equal-width example chooses `ell = L` and all consecutive source layers as
selected cutpoints.  This is only the equal-width example, not arbitrary
selected-cutpoint existence. -/
theorem exists_consecutive_of_constant_reducedWidth_pos
    {L : ℕ} {H : ℕ → ℕ} {r w : ℕ}
    (hL : 0 < L) (hw : 0 < w)
    (hconst :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        aoyagiReducedWidthInt H r s = (w : ℤ)) :
    ∃ C : AoyagiSelectedCutpoints L,
      (∀ j : Fin (L + 1), C.cut j = j.val + 1) ∧
        AoyagiDefinition3SourceData L L H r C := by
  classical
  let C : AoyagiSelectedCutpoints L :=
    { cut := fun j ↦ j.val + 1
      pos := by
        intro j
        omega
      strict := by
        intro j
        simp [Fin.val_succ, Fin.val_castSucc] }
  refine ⟨C, ?_, ?_⟩
  · intro j
    rfl
  · have hsum :
        (∑ j : Fin (L + 1), aoyagiReducedWidthInt H r (C.cut j)) =
          ((L + 1 : ℕ) : ℤ) * (w : ℤ) := by
      calc
        (∑ j : Fin (L + 1), aoyagiReducedWidthInt H r (C.cut j)) =
            ∑ _j : Fin (L + 1), (w : ℤ) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact hconst (C.cut j) (C.pos j) (by dsimp [C]; omega)
        _ = ((L + 1 : ℕ) : ℤ) * (w : ℤ) := by
          simp [Finset.sum_const, Fintype.card_fin]
    have hselected_mem :
        ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
          aoyagiReducedWidthInt H r s ∈
            Finset.univ.image
              (fun j : Fin (L + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
      intro s hs1 hsL
      rw [hconst s hs1 hsL]
      refine Finset.mem_image.mpr ⟨(0 : Fin (L + 1)), Finset.mem_univ _, ?_⟩
      exact hconst (C.cut (0 : Fin (L + 1))) (C.pos _) (by dsimp [C]; omega)
    refine
      { ell_pos := hL
        cut_le := ?_
        selected_strict := ?_
        selected_lt_nonselected := ?_
        nonselected_le := ?_ }
    · intro j
      dsimp [C]
      omega
    · intro i
      rw [hconst (C.cut i) (C.pos i) (by dsimp [C]; omega), hsum]
      have hwz : (0 : ℤ) < (w : ℤ) := by exact_mod_cast hw
      have hlt : (L : ℤ) * (w : ℤ) < ((L : ℤ) + 1) * (w : ℤ) := by
        nlinarith
      simpa [Nat.cast_add, Nat.cast_one] using hlt
    · intro _i s hs1 hsL hnot
      exact False.elim (hnot (hselected_mem s hs1 hsL))
    · intro s hs1 hsL hnot
      exact False.elim (hnot (hselected_mem s hs1 hsL))

/-- Source data when all source layers are selected.

This chooses consecutive cutpoints `C.cut j = j.val + 1`.  The nonselected
fields are vacuous because every source-range reduced-width value belongs to
the selected value set. -/
theorem exists_consecutive_of_all_selected_strict
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hL : 0 < L)
    (hstrict :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        (L : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (L + 1), aoyagiReducedWidthInt H r (j.val + 1)) :
    ∃ C : AoyagiSelectedCutpoints L,
      (∀ j : Fin (L + 1), C.cut j = j.val + 1) ∧
        AoyagiDefinition3SourceData L L H r C := by
  classical
  let C : AoyagiSelectedCutpoints L :=
    { cut := fun j ↦ j.val + 1
      pos := by
        intro j
        omega
      strict := by
        intro j
        simp [Fin.val_succ, Fin.val_castSucc] }
  have hselected_mem :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        aoyagiReducedWidthInt H r s ∈
          Finset.univ.image
            (fun j : Fin (L + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
    intro s hs1 hsL
    let j : Fin (L + 1) := ⟨s - 1, by omega⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    have hcut : C.cut j = s := by
      dsimp [C, j]
      omega
    rw [hcut]
  refine ⟨C, ?_, ?_⟩
  · intro j
    rfl
  · refine
      { ell_pos := hL
        cut_le := ?_
        selected_strict := ?_
        selected_lt_nonselected := ?_
        nonselected_le := ?_ }
    · intro j
      dsimp [C]
      omega
    · intro i
      have hi1 : 1 ≤ C.cut i := C.pos i
      have hiL : C.cut i ≤ L + 1 := by
        dsimp [C]
        omega
      have hsum :
          (∑ j : Fin (L + 1), aoyagiReducedWidthInt H r (C.cut j)) =
            ∑ j : Fin (L + 1), aoyagiReducedWidthInt H r (j.val + 1) := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rfl
      rw [hsum]
      exact hstrict (C.cut i) hi1 hiL
    · intro _i s hs1 hsL hnot
      exact False.elim (hnot (hselected_mem s hs1 hsL))
    · intro s hs1 hsL hnot
      exact False.elim (hnot (hselected_mem s hs1 hsL))

/-- A constant Nat-valued reduced-width identity implies the source-range
rank-width bound used by the selected-width ceiling package. -/
theorem sourceRangeRankWidth_of_constant_reducedWidth
    {L : ℕ} {H : ℕ → ℕ} {r w : ℕ}
    (hconst :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        aoyagiReducedWidthInt H r s = (w : ℤ)) :
    ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s := by
  intro s hs1 hsL
  have hnonneg : 0 ≤ aoyagiReducedWidthInt H r s := by
    rw [hconst s hs1 hsL]
    exact_mod_cast Nat.zero_le w
  unfold aoyagiReducedWidthInt at hnonneg
  exact_mod_cast (sub_nonneg.mp hnonneg)

/-- If an integer reduced width is identified with a natural number, the
underlying rank-width bound holds at that source layer. -/
theorem rank_le_of_aoyagiReducedWidthInt_eq_natCast
    {H : ℕ → ℕ} {r s w : ℕ}
    (hw : aoyagiReducedWidthInt H r s = (w : ℤ)) :
    r ≤ H s := by
  have hnonneg : 0 ≤ aoyagiReducedWidthInt H r s := by
    rw [hw]
    exact_mod_cast Nat.zero_le w
  unfold aoyagiReducedWidthInt at hnonneg
  exact_mod_cast (sub_nonneg.mp hnonneg)

/-- Three Nat-valued reduced-width identities give the source-range rank-width
bound for `L=2`. -/
theorem sourceRangeRankWidth_of_three_reducedWidthInt_eq_natCast
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ)) :
    ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s := by
  intro s hs1 hsL
  have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hs with rfl | rfl | rfl
  · exact rank_le_of_aoyagiReducedWidthInt_eq_natCast hw1
  · exact rank_le_of_aoyagiReducedWidthInt_eq_natCast hw2
  · exact rank_le_of_aoyagiReducedWidthInt_eq_natCast hw3

/-- The all-source strict selected inequalities force source-range rank-width.

For a fixed source index, sum the strict inequalities over the other `L`
source indices.  Since there are exactly `L` of them and `0 < L`, cancellation
shows the fixed reduced width is positive. -/
theorem sourceRangeRankWidth_of_all_selected_strict
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hL : 0 < L)
    (hstrict :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        (L : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (L + 1), aoyagiReducedWidthInt H r (j.val + 1)) :
    ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s := by
  classical
  intro s hs1 hsL
  let i : Fin (L + 1) := ⟨s - 1, by omega⟩
  let f : Fin (L + 1) → ℤ :=
    fun j ↦ aoyagiReducedWidthInt H r (j.val + 1)
  let T : ℤ := ∑ j : Fin (L + 1), f j
  have hi_val : i.val + 1 = s := by
    dsimp [i]
    omega
  have hstrict_fin : ∀ j : Fin (L + 1), (L : ℤ) * f j < T := by
    intro j
    dsimp [f, T]
    exact hstrict (j.val + 1) (by omega) (by omega)
  let k : Fin (L + 1) := if i.val = 0 then Fin.last L else 0
  have hk_ne : k ≠ i := by
    by_cases hi0 : i.val = 0
    · dsimp [k]
      rw [if_pos hi0]
      intro hki
      have hval : L = 0 := by
        have := congrArg Fin.val hki
        simp [hi0] at this
        omega
      omega
    · dsimp [k]
      rw [if_neg hi0]
      intro hki
      exact hi0 (congrArg Fin.val hki).symm
  have hk_mem : k ∈ Finset.univ.erase i := by
    simp [hk_ne]
  have hsum_erase_lt :
      ∑ j ∈ (Finset.univ.erase i), (L : ℤ) * f j <
        ∑ _j ∈ (Finset.univ.erase i), T := by
    exact Finset.sum_lt_sum
      (fun j _hj ↦ le_of_lt (hstrict_fin j))
      ⟨k, hk_mem, hstrict_fin k⟩
  have hcard_erase : (Finset.univ.erase i).card = L := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hleft :
      ∑ j ∈ (Finset.univ.erase i), (L : ℤ) * f j =
        (L : ℤ) * ∑ j ∈ (Finset.univ.erase i), f j := by
    rw [Finset.mul_sum]
  have hright :
      ∑ _j ∈ (Finset.univ.erase i), T = (L : ℤ) * T := by
    rw [Finset.sum_const, hcard_erase]
    norm_num [nsmul_eq_mul]
  have hmul :
      (L : ℤ) * (∑ j ∈ (Finset.univ.erase i), f j) < (L : ℤ) * T := by
    rwa [hleft, hright] at hsum_erase_lt
  have hLz_pos : (0 : ℤ) < (L : ℤ) := by
    exact_mod_cast hL
  have herase_lt_T : ∑ j ∈ (Finset.univ.erase i), f j < T :=
    lt_of_mul_lt_mul_left hmul (le_of_lt hLz_pos)
  have hsum_univ :
      T = f i + ∑ j ∈ (Finset.univ.erase i), f j := by
    dsimp [T]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    ring
  have hfi_pos : 0 < f i := by
    rw [hsum_univ] at herase_lt_T
    omega
  have hred_pos : 0 < aoyagiReducedWidthInt H r s := by
    dsimp [f] at hfi_pos
    rwa [hi_val] at hfi_pos
  unfold aoyagiReducedWidthInt at hred_pos
  have hri : (r : ℤ) < (H s : ℤ) := by omega
  exact_mod_cast le_of_lt hri

/-- Diagnostic obstruction: the printed Definition 3 inequalities do not
produce source data for the reduced-width profile `1,2,100`.

This is a guardrail against proving arbitrary selected-cutpoint/source-data
existence from the printed inequalities.  It is not a statement about all
width profiles, and it does not affect the supplied-source-data API. -/
theorem not_exists_widths_one_two_hundred :
    let H : ℕ → ℕ :=
      fun s ↦
        if s = 1 then 1 else if s = 2 then 2 else if s = 3 then 100 else 0
    ¬ ∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
      AoyagiDefinition3SourceData 2 ell H 0 C := by
  let H : ℕ → ℕ :=
    fun s ↦
      if s = 1 then 1 else if s = 2 then 2 else if s = 3 then 100 else 0
  change ¬ ∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
    AoyagiDefinition3SourceData 2 ell H 0 C
  rintro ⟨ell, C, S⟩
  have hell_le : ell ≤ 2 := by
    by_contra hnot
    have hell3 : 3 ≤ ell := by omega
    have h0pos : 1 ≤ C.cut (⟨0, by omega⟩ : Fin (ell + 1)) :=
      C.pos _
    have h01 :
        C.cut (⟨0, by omega⟩ : Fin (ell + 1)) <
          C.cut (⟨1, by omega⟩ : Fin (ell + 1)) :=
      C.cut_strictMono (by
        change (0 : ℕ) < 1
        norm_num)
    have h12 :
        C.cut (⟨1, by omega⟩ : Fin (ell + 1)) <
          C.cut (⟨2, by omega⟩ : Fin (ell + 1)) :=
      C.cut_strictMono (by
        change (1 : ℕ) < 2
        norm_num)
    have h23 :
        C.cut (⟨2, by omega⟩ : Fin (ell + 1)) <
          C.cut (⟨3, by omega⟩ : Fin (ell + 1)) :=
      C.cut_strictMono (by
        change (2 : ℕ) < 3
        norm_num)
    have h3le : C.cut (⟨3, by omega⟩ : Fin (ell + 1)) ≤ 3 := by
      simpa using S.cut_le (⟨3, by omega⟩ : Fin (ell + 1))
    omega
  have hell_pos : 0 < ell := S.ell_pos
  interval_cases ell
  · have h0pos : 1 ≤ C.cut (0 : Fin 2) := C.pos _
    have h0le : C.cut (0 : Fin 2) ≤ 3 := by
      simpa using S.cut_le (0 : Fin 2)
    have h1pos : 1 ≤ C.cut (1 : Fin 2) := C.pos _
    have h1le : C.cut (1 : Fin 2) ≤ 3 := by
      simpa using S.cut_le (1 : Fin 2)
    have h01 : C.cut (0 : Fin 2) < C.cut (1 : Fin 2) :=
      C.cut_strictMono (by
        change (0 : ℕ) < 1
        norm_num)
    have h0_cases :
        C.cut (0 : Fin 2) = 1 ∨ C.cut (0 : Fin 2) = 2 ∨
          C.cut (0 : Fin 2) = 3 := by
      omega
    have h1_cases :
        C.cut (1 : Fin 2) = 1 ∨ C.cut (1 : Fin 2) = 2 ∨
          C.cut (1 : Fin 2) = 3 := by
      omega
    rcases h0_cases with h0 | h0 | h0
    · rcases h1_cases with h1 | h1 | h1
      · omega
      · have hnot :
            aoyagiReducedWidthInt H 0 3 ∉
              Finset.univ.image
                (fun j : Fin (1 + 1) ↦
                  aoyagiReducedWidthInt H 0 (C.cut j)) := by
          intro hm
          rw [Finset.mem_image] at hm
          rcases hm with ⟨j, -, hj⟩
          fin_cases j <;> norm_num [aoyagiReducedWidthInt, H, h0, h1] at hj
        have hle := S.nonselected_le 3 (by norm_num) (by norm_num) hnot
        have hsum :
            (∑ x : Fin (1 + 1), aoyagiReducedWidthInt H 0 (C.cut x)) = 3 := by
          rw [Fin.sum_univ_two]
          norm_num [aoyagiReducedWidthInt, H, h0, h1]
        rw [hsum] at hle
        norm_num [aoyagiReducedWidthInt, H] at hle
      · have hnot :
            aoyagiReducedWidthInt H 0 2 ∉
              Finset.univ.image
                (fun j : Fin (1 + 1) ↦
                  aoyagiReducedWidthInt H 0 (C.cut j)) := by
          intro hm
          rw [Finset.mem_image] at hm
          rcases hm with ⟨j, -, hj⟩
          fin_cases j <;> norm_num [aoyagiReducedWidthInt, H, h0, h1] at hj
        have hle := S.nonselected_le 2 (by norm_num) (by norm_num) hnot
        have hsum :
            (∑ x : Fin (1 + 1), aoyagiReducedWidthInt H 0 (C.cut x)) = 101 := by
          rw [Fin.sum_univ_two]
          norm_num [aoyagiReducedWidthInt, H, h0, h1]
        rw [hsum] at hle
        norm_num [aoyagiReducedWidthInt, H] at hle
    · rcases h1_cases with h1 | h1 | h1
      · omega
      · omega
      · have hnot :
            aoyagiReducedWidthInt H 0 1 ∉
              Finset.univ.image
                (fun j : Fin (1 + 1) ↦
                  aoyagiReducedWidthInt H 0 (C.cut j)) := by
          intro hm
          rw [Finset.mem_image] at hm
          rcases hm with ⟨j, -, hj⟩
          fin_cases j <;> norm_num [aoyagiReducedWidthInt, H, h0, h1] at hj
        have hle := S.nonselected_le 1 (by norm_num) (by norm_num) hnot
        have hsum :
            (∑ x : Fin (1 + 1), aoyagiReducedWidthInt H 0 (C.cut x)) = 102 := by
          rw [Fin.sum_univ_two]
          norm_num [aoyagiReducedWidthInt, H, h0, h1]
        rw [hsum] at hle
        norm_num [aoyagiReducedWidthInt, H] at hle
    · rcases h1_cases with h1 | h1 | h1 <;> omega
  · have h0pos : 1 ≤ C.cut (0 : Fin 3) := C.pos _
    have h0le : C.cut (0 : Fin 3) ≤ 3 := by
      simpa using S.cut_le (0 : Fin 3)
    have h1pos : 1 ≤ C.cut (1 : Fin 3) := C.pos _
    have h1le : C.cut (1 : Fin 3) ≤ 3 := by
      simpa using S.cut_le (1 : Fin 3)
    have h2pos : 1 ≤ C.cut (2 : Fin 3) := C.pos _
    have h2le : C.cut (2 : Fin 3) ≤ 3 := by
      simpa using S.cut_le (2 : Fin 3)
    have h01 : C.cut (0 : Fin 3) < C.cut (1 : Fin 3) :=
      C.cut_strictMono (by
        change (0 : ℕ) < 1
        norm_num)
    have h12 : C.cut (1 : Fin 3) < C.cut (2 : Fin 3) :=
      C.cut_strictMono (by
        change (1 : ℕ) < 2
        norm_num)
    have h0 : C.cut (0 : Fin 3) = 1 := by omega
    have h1 : C.cut (1 : Fin 3) = 2 := by omega
    have h2 : C.cut (2 : Fin 3) = 3 := by omega
    have hstrict := S.selected_strict (2 : Fin 3)
    have hsum :
        (∑ x : Fin (2 + 1), aoyagiReducedWidthInt H 0 (C.cut x)) = 103 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_two]
      norm_num [aoyagiReducedWidthInt, H, h0, h1, h2]
    rw [hsum] at hstrict
    norm_num [aoyagiReducedWidthInt, H, h2] at hstrict

/-- For `ell = 1`, Definition 3 source data has no genuinely nonselected
source-range reduced-width value.

The printed nonselected inequality has coefficient `ell - 1 = 0`; the two
strict selected inequalities already force the selected sum to be positive,
so a genuine nonselected value is impossible.  This is only a necessary
condition for supplied source data, not selected-cutpoint construction. -/
theorem reducedWidth_mem_selectedValueSet_of_ell_eq_one
    {L : ℕ} {H : ℕ → ℕ} {r s : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (S : AoyagiDefinition3SourceData L 1 H r C)
    (hs1 : 1 ≤ s) (hsL : s ≤ L + 1) :
    aoyagiReducedWidthInt H r s ∈
      Finset.univ.image
        (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
  by_contra hnot
  have hle := S.nonselected_le s hs1 hsL hnot
  have hle0 :
      (∑ j : Fin (1 + 1), aoyagiReducedWidthInt H r (C.cut j)) ≤ 0 := by
    norm_num at hle ⊢
    simpa using hle
  have h0pos : 0 < aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) := by
    have hstrict := S.selected_strict (1 : Fin (1 + 1))
    rw [Fin.sum_univ_two] at hstrict
    norm_num at hstrict
    omega
  have h1pos : 0 < aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) := by
    have hstrict := S.selected_strict (0 : Fin (1 + 1))
    rw [Fin.sum_univ_two] at hstrict
    norm_num at hstrict
    omega
  have hsum_pos :
      0 < ∑ j : Fin (1 + 1), aoyagiReducedWidthInt H r (C.cut j) := by
    rw [Fin.sum_univ_two]
    omega
  omega

/-- Rank-width version of the `ell = 1` necessary condition.

The rank-width hypothesis is retained for callers that already provide it, but
it is no longer needed by the proof. -/
theorem reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
    {L : ℕ} {H : ℕ → ℕ} {r s : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (S : AoyagiDefinition3SourceData L 1 H r C)
    (_hr : ∀ t : ℕ, 1 ≤ t → t ≤ L + 1 → r ≤ H t)
    (hs1 : 1 ≤ s) (hsL : s ≤ L + 1) :
    aoyagiReducedWidthInt H r s ∈
      Finset.univ.image
        (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) :=
  S.reducedWidth_mem_selectedValueSet_of_ell_eq_one hs1 hsL

/-- For `ell = 1`, Definition 3 source data forces source-range rank-width.

Every source-range reduced width is one of the two selected values, and the
two strict selected inequalities make both selected values positive. -/
theorem sourceRangeRankWidth_of_ell_eq_one
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (S : AoyagiDefinition3SourceData L 1 H r C) :
    ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s := by
  intro s hs1 hsL
  have h0pos : 0 < aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) := by
    have hstrict := S.selected_strict (1 : Fin (1 + 1))
    rw [Fin.sum_univ_two] at hstrict
    norm_num at hstrict
    omega
  have h1pos : 0 < aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) := by
    have hstrict := S.selected_strict (0 : Fin (1 + 1))
    rw [Fin.sum_univ_two] at hstrict
    norm_num at hstrict
    omega
  have hmem :=
    S.reducedWidth_mem_selectedValueSet_of_ell_eq_one hs1 hsL
  rcases Finset.mem_image.mp hmem with ⟨j, _hj, hjs⟩
  have hnonneg : 0 ≤ aoyagiReducedWidthInt H r s := by
    fin_cases j
    · rw [← hjs]
      exact le_of_lt h0pos
    · rw [← hjs]
      exact le_of_lt h1pos
  unfold aoyagiReducedWidthInt at hnonneg
  exact_mod_cast (sub_nonneg.mp hnonneg)

/-- Constructor for `ell = 1` source data when the two selected values are
positive and cover every source-range reduced-width value.

The nonselected clauses are vacuous because the supplied cover is by value,
matching Aoyagi Definition 3's selected value set. -/
theorem of_ell_eq_one_selectedValueSet_covers
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ L + 1)
    (h0pos : 0 < aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))))
    (h1pos : 0 < aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))))
    (hcover : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
      aoyagiReducedWidthInt H r s ∈
        Finset.univ.image
          (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j))) :
    AoyagiDefinition3SourceData L 1 H r C where
  ell_pos := by norm_num
  cut_le := hcut_le
  selected_strict := by
    intro i
    fin_cases i
    · rw [Fin.sum_univ_two]
      norm_num
      omega
    · rw [Fin.sum_univ_two]
      norm_num
      omega
  selected_lt_nonselected := by
    intro _i s hs1 hsL hnot
    exact False.elim (hnot (hcover s hs1 hsL))
  nonselected_le := by
    intro s hs1 hsL hnot
    exact False.elim (hnot (hcover s hs1 hsL))

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

/-- All-source selected source data together with the downstream selected
reduced-width ceiling package.

This packages the all-source selected constructor with the rank-width
hypothesis needed to rewrite reduced widths as natural layer-width
differences.  It does not compute the ceiling datum in closed form. -/
theorem exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hL : 0 < L)
    (hstrict :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        (L : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (L + 1), aoyagiReducedWidthInt H r (j.val + 1))
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s) :
    ∃ (C : AoyagiSelectedCutpoints L)
        (m : Fin (L + 1) → ℤ)
        (data : AoyagiDefinition3CeilData L m),
      (∀ j : Fin (L + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData L L H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (L + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (L + 1), 0 ≤ m j) ∧
      (∀ i : Fin (L + 1),
        (L : ℤ) * m i < ∑ j : Fin (L + 1), m j) ∧
      (∀ i : Fin (L + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat L m i) := by
  rcases exists_consecutive_of_all_selected_strict
      (L := L) (H := H) (r := r) hL hstrict with
    ⟨C, hC, S⟩
  rcases S.exists_selectedReducedWidthCeilData_of_rankWidth hr with
    ⟨m, data, hm, hnat, hnonneg, hstrict_m, hle, hnatNonneg⟩
  exact ⟨C, m, data, hC, S, hm, hnat, hnonneg, hstrict_m, hle, hnatNonneg⟩

/-- All-source selected source data and ceiling package from strictness alone.

The all-source strict inequalities already force the source-range rank-width
bound used to rewrite reduced widths as natural layer-width differences. -/
theorem exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    (hL : 0 < L)
    (hstrict :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        (L : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (L + 1), aoyagiReducedWidthInt H r (j.val + 1)) :
    ∃ (C : AoyagiSelectedCutpoints L)
        (m : Fin (L + 1) → ℤ)
        (data : AoyagiDefinition3CeilData L m),
      (∀ j : Fin (L + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData L L H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (L + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (L + 1), 0 ≤ m j) ∧
      (∀ i : Fin (L + 1),
        (L : ℤ) * m i < ∑ j : Fin (L + 1), m j) ∧
      (∀ i : Fin (L + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat L m i) := by
  exact exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth
    hL hstrict
    (sourceRangeRankWidth_of_all_selected_strict hL hstrict)

/-- For `L=2`, pairwise distinct source-range reduced widths force any
Definition 3 source-data choice to use `ell=2`.

The only other possible positive value is `ell=1`; the existing `ell=1`
obstruction says every source-range reduced-width value would then lie in the
two selected values, contradicting pairwise distinctness of the three source
values. -/
theorem ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData 2 ell H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s)
    (h12 : aoyagiReducedWidthInt H r 1 ≠ aoyagiReducedWidthInt H r 2)
    (h13 : aoyagiReducedWidthInt H r 1 ≠ aoyagiReducedWidthInt H r 3)
    (h23 : aoyagiReducedWidthInt H r 2 ≠ aoyagiReducedWidthInt H r 3) :
    ell = 2 := by
  have hell_le : ell ≤ 2 := by
    by_contra hnot
    have hell3 : 3 ≤ ell := by omega
    have h0pos :
        1 ≤ C.cut (⟨0, by omega⟩ : Fin (ell + 1)) := C.pos _
    have h01 :
        C.cut (⟨0, by omega⟩ : Fin (ell + 1)) <
          C.cut (⟨1, by omega⟩ : Fin (ell + 1)) :=
      C.cut_strictMono (by
        change (0 : ℕ) < 1
        norm_num)
    have h12cut :
        C.cut (⟨1, by omega⟩ : Fin (ell + 1)) <
          C.cut (⟨2, by omega⟩ : Fin (ell + 1)) :=
      C.cut_strictMono (by
        change (1 : ℕ) < 2
        norm_num)
    have h23cut :
        C.cut (⟨2, by omega⟩ : Fin (ell + 1)) <
          C.cut (⟨3, by omega⟩ : Fin (ell + 1)) :=
      C.cut_strictMono (by
        change (2 : ℕ) < 3
        norm_num)
    have h3le :
        C.cut (⟨3, by omega⟩ : Fin (ell + 1)) ≤ 3 := by
      simpa using S.cut_le (⟨3, by omega⟩ : Fin (ell + 1))
    omega
  have hell_pos : 0 < ell := S.ell_pos
  interval_cases ell
  · have hmem1 :
        aoyagiReducedWidthInt H r 1 ∈
          Finset.univ.image
            (fun j : Fin (1 + 1) ↦
              aoyagiReducedWidthInt H r (C.cut j)) :=
      S.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
        hr (by norm_num) (by norm_num)
    have hmem2 :
        aoyagiReducedWidthInt H r 2 ∈
          Finset.univ.image
            (fun j : Fin (1 + 1) ↦
              aoyagiReducedWidthInt H r (C.cut j)) :=
      S.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
        hr (by norm_num) (by norm_num)
    have hmem3 :
        aoyagiReducedWidthInt H r 3 ∈
          Finset.univ.image
            (fun j : Fin (1 + 1) ↦
              aoyagiReducedWidthInt H r (C.cut j)) :=
      S.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
        hr (by norm_num) (by norm_num)
    have h0pos : 1 ≤ C.cut (0 : Fin (1 + 1)) := C.pos _
    have h0le : C.cut (0 : Fin (1 + 1)) ≤ 3 := by
      simpa using S.cut_le (0 : Fin (1 + 1))
    have h1pos : 1 ≤ C.cut (1 : Fin (1 + 1)) := C.pos _
    have h1le : C.cut (1 : Fin (1 + 1)) ≤ 3 := by
      simpa using S.cut_le (1 : Fin (1 + 1))
    have h01 : C.cut (0 : Fin (1 + 1)) < C.cut (1 : Fin (1 + 1)) :=
      C.cut_strictMono (by
        change (0 : ℕ) < 1
        norm_num)
    have h0_cases :
        C.cut (0 : Fin (1 + 1)) = 1 ∨
          C.cut (0 : Fin (1 + 1)) = 2 ∨
          C.cut (0 : Fin (1 + 1)) = 3 := by
      omega
    have h1_cases :
        C.cut (1 : Fin (1 + 1)) = 1 ∨
          C.cut (1 : Fin (1 + 1)) = 2 ∨
          C.cut (1 : Fin (1 + 1)) = 3 := by
      omega
    rcases h0_cases with h0 | h0 | h0
    · rcases h1_cases with h1 | h1 | h1
      · omega
      · have hnot3 :
            aoyagiReducedWidthInt H r 3 ∉
              Finset.univ.image
                (fun j : Fin (1 + 1) ↦
                  aoyagiReducedWidthInt H r (C.cut j)) := by
          intro hm
          rw [Finset.mem_image] at hm
          rcases hm with ⟨j, -, hj⟩
          fin_cases j
          · exact h13 (by simpa [h0] using hj)
          · exact h23 (by simpa [h1] using hj)
        exact False.elim (hnot3 hmem3)
      · have hnot2 :
            aoyagiReducedWidthInt H r 2 ∉
              Finset.univ.image
                (fun j : Fin (1 + 1) ↦
                  aoyagiReducedWidthInt H r (C.cut j)) := by
          intro hm
          rw [Finset.mem_image] at hm
          rcases hm with ⟨j, -, hj⟩
          fin_cases j
          · exact h12 (by simpa [h0] using hj)
          · exact h23 (by simpa [h1] using hj.symm)
        exact False.elim (hnot2 hmem2)
    · rcases h1_cases with h1 | h1 | h1
      · omega
      · omega
      · have hnot1 :
            aoyagiReducedWidthInt H r 1 ∉
              Finset.univ.image
                (fun j : Fin (1 + 1) ↦
                  aoyagiReducedWidthInt H r (C.cut j)) := by
          intro hm
          rw [Finset.mem_image] at hm
          rcases hm with ⟨j, -, hj⟩
          fin_cases j
          · exact h12 (by simpa [h0] using hj.symm)
          · exact h13 (by simpa [h1] using hj.symm)
        exact False.elim (hnot1 hmem1)
    · rcases h1_cases with h1 | h1 | h1 <;> omega
  · rfl

/-- With `L=2` and `ell=2`, any Definition 3 source-data cutpoints are the
consecutive source layers `1,2,3`. -/
theorem cut_eq_consecutive_of_L_eq_two
    {H : ℕ → ℕ} {r : ℕ} {C : AoyagiSelectedCutpoints 2}
    (S : AoyagiDefinition3SourceData 2 2 H r C) :
    ∀ j : Fin (2 + 1), C.cut j = j.val + 1 := by
  have h0pos : 1 ≤ C.cut (0 : Fin (2 + 1)) := C.pos _
  have h01 : C.cut (0 : Fin (2 + 1)) < C.cut (1 : Fin (2 + 1)) :=
    C.cut_strictMono (by
      change (0 : ℕ) < 1
      norm_num)
  have h12cut : C.cut (1 : Fin (2 + 1)) < C.cut (2 : Fin (2 + 1)) :=
    C.cut_strictMono (by
      change (1 : ℕ) < 2
      norm_num)
  have h2le : C.cut (2 : Fin (2 + 1)) ≤ 3 := by
    simpa using S.cut_le (2 : Fin (2 + 1))
  have h0 : C.cut (0 : Fin (2 + 1)) = 1 := by omega
  have h1 : C.cut (1 : Fin (2 + 1)) = 2 := by omega
  have h2 : C.cut (2 : Fin (2 + 1)) = 3 := by omega
  intro j
  fin_cases j <;> simp [h0, h1, h2]

/-- For `L=2` and pairwise distinct source-range reduced widths, existence of
Definition 3 source data is equivalent to the all-source strict selected
inequalities.

This is a finite Definition 3 classification only for the pairwise-distinct
three-layer source range.  It does not classify repeated-width profiles. -/
theorem exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct
    {H : ℕ → ℕ} {r : ℕ}
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s)
    (h12 : aoyagiReducedWidthInt H r 1 ≠ aoyagiReducedWidthInt H r 2)
    (h13 : aoyagiReducedWidthInt H r 1 ≠ aoyagiReducedWidthInt H r 3)
    (h23 : aoyagiReducedWidthInt H r 2 ≠ aoyagiReducedWidthInt H r 3) :
    (∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
      AoyagiDefinition3SourceData 2 ell H r C) ↔
      ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
        (2 : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1) := by
  constructor
  · rintro ⟨ell, C, S⟩
    have hell :
        ell = 2 :=
      S.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct hr h12 h13 h23
    subst ell
    have hC : ∀ j : Fin (2 + 1), C.cut j = j.val + 1 :=
      S.cut_eq_consecutive_of_L_eq_two
    have hsum :
        (∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (C.cut j)) =
          ∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1) := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [hC j]
    intro s hs1 hsL
    let j : Fin (2 + 1) := ⟨s - 1, by omega⟩
    have hcut : C.cut j = s := by
      rw [hC j]
      dsimp [j]
      omega
    have hstrict := S.selected_strict j
    rw [hcut, hsum] at hstrict
    simpa using hstrict
  · intro hstrict
    rcases exists_consecutive_of_all_selected_strict
        (L := 2) (H := H) (r := r) (by norm_num) hstrict with
      ⟨C, _hC, S⟩
    exact ⟨2, C, S⟩

/-- Positive repeated reduced widths give an `ell = 1` Definition 3 source-data
witness for `L=2`.

The selected cutpoints are chosen so that their two values cover all three
source-range reduced-width values. -/
theorem exists_ell_one_of_L_eq_two_positive_repeated
    {H : ℕ → ℕ} {r : ℕ}
    (hpos1 : 0 < aoyagiReducedWidthInt H r 1)
    (hpos2 : 0 < aoyagiReducedWidthInt H r 2)
    (hpos3 : 0 < aoyagiReducedWidthInt H r 3)
    (hrep :
      aoyagiReducedWidthInt H r 1 = aoyagiReducedWidthInt H r 2 ∨
        aoyagiReducedWidthInt H r 1 = aoyagiReducedWidthInt H r 3 ∨
        aoyagiReducedWidthInt H r 2 = aoyagiReducedWidthInt H r 3) :
    ∃ C : AoyagiSelectedCutpoints 1,
      AoyagiDefinition3SourceData 2 1 H r C := by
  rcases hrep with h12 | h13 | h23
  · let C : AoyagiSelectedCutpoints 1 :=
      { cut := fun j ↦ if j = (0 : Fin (1 + 1)) then 1 else 3
        pos := by
          intro j
          fin_cases j <;> simp
        strict := by
          intro j
          fin_cases j
          simp }
    refine ⟨C, ?_⟩
    refine of_ell_eq_one_selectedValueSet_covers
      (L := 2) (H := H) (r := r) (C := C) ?_ ?_ ?_ ?_
    · intro j
      fin_cases j <;> norm_num [C]
    · simpa [C] using hpos1
    · simpa [C] using hpos3
    · intro s hs1 hsL
      have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
      rcases hs with rfl | rfl | rfl
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simpa [C] using h12
      · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
  · let C : AoyagiSelectedCutpoints 1 :=
      { cut := fun j ↦ j.val + 1
        pos := by
          intro j
          omega
        strict := by
          intro j
          fin_cases j
          simp }
    refine ⟨C, ?_⟩
    refine of_ell_eq_one_selectedValueSet_covers
      (L := 2) (H := H) (r := r) (C := C) ?_ ?_ ?_ ?_
    · intro j
      fin_cases j <;> norm_num [C]
    · simpa [C] using hpos1
    · simpa [C] using hpos2
    · intro s hs1 hsL
      have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
      rcases hs with rfl | rfl | rfl
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
      · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simpa [C] using h13
  · let C : AoyagiSelectedCutpoints 1 :=
      { cut := fun j ↦ j.val + 1
        pos := by
          intro j
          omega
        strict := by
          intro j
          fin_cases j
          simp }
    refine ⟨C, ?_⟩
    refine of_ell_eq_one_selectedValueSet_covers
      (L := 2) (H := H) (r := r) (C := C) ?_ ?_ ?_ ?_
    · intro j
      fin_cases j <;> norm_num [C]
    · simpa [C] using hpos1
    · simpa [C] using hpos2
    · intro s hs1 hsL
      have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
      rcases hs with rfl | rfl | rfl
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
      · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
      · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simpa [C] using h23

/-- Exact `ell = 1` part of the complete finite `L=2` Definition 3
classification.

For three source layers, an `ell=1` source datum exists precisely when all
three source-range reduced widths are positive and two of them repeat. -/
theorem exists_ell_one_sourceData_iff_repeatedPositive_of_L_eq_two
    {H : ℕ → ℕ} {r : ℕ} :
    (∃ C : AoyagiSelectedCutpoints 1,
      AoyagiDefinition3SourceData 2 1 H r C) ↔
      ((0 : ℤ) < aoyagiReducedWidthInt H r 1 ∧
        (0 : ℤ) < aoyagiReducedWidthInt H r 2 ∧
        (0 : ℤ) < aoyagiReducedWidthInt H r 3 ∧
        (aoyagiReducedWidthInt H r 1 = aoyagiReducedWidthInt H r 2 ∨
          aoyagiReducedWidthInt H r 1 = aoyagiReducedWidthInt H r 3 ∨
          aoyagiReducedWidthInt H r 2 = aoyagiReducedWidthInt H r 3)) := by
  constructor
  · rintro ⟨C, S⟩
    have hmem1 :=
      S.reducedWidth_mem_selectedValueSet_of_ell_eq_one
        (s := 1) (by norm_num) (by norm_num)
    have hmem2 :=
      S.reducedWidth_mem_selectedValueSet_of_ell_eq_one
        (s := 2) (by norm_num) (by norm_num)
    have hmem3 :=
      S.reducedWidth_mem_selectedValueSet_of_ell_eq_one
        (s := 3) (by norm_num) (by norm_num)
    have hsel0pos :
        0 < aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) := by
      have hstrict := S.selected_strict (1 : Fin (1 + 1))
      rw [Fin.sum_univ_two] at hstrict
      norm_num at hstrict
      omega
    have hsel1pos :
        0 < aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) := by
      have hstrict := S.selected_strict (0 : Fin (1 + 1))
      rw [Fin.sum_univ_two] at hstrict
      norm_num at hstrict
      omega
    have hpos_of_mem : ∀ {s : ℕ},
        aoyagiReducedWidthInt H r s ∈
          Finset.univ.image
            (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) →
        0 < aoyagiReducedWidthInt H r s := by
      intro s hm
      rw [Finset.mem_image] at hm
      rcases hm with ⟨j, _hjmem, hj⟩
      fin_cases j
      · exact hj ▸ hsel0pos
      · exact hj ▸ hsel1pos
    refine ⟨hpos_of_mem hmem1, hpos_of_mem hmem2, hpos_of_mem hmem3, ?_⟩
    rw [Finset.mem_image] at hmem1 hmem2 hmem3
    rcases hmem1 with ⟨j1, _hj1mem, hj1⟩
    rcases hmem2 with ⟨j2, _hj2mem, hj2⟩
    rcases hmem3 with ⟨j3, _hj3mem, hj3⟩
    have hpigeon : j1 = j2 ∨ j1 = j3 ∨ j2 = j3 := by
      fin_cases j1 <;> fin_cases j2 <;> fin_cases j3 <;> simp
    rcases hpigeon with h12j | h13j | h23j
    · left
      subst j2
      exact hj1.symm.trans hj2
    · right
      left
      subst j3
      exact hj1.symm.trans hj3
    · right
      right
      subst j3
      exact hj2.symm.trans hj3
  · rintro ⟨hpos1, hpos2, hpos3, hrep⟩
    exact
      exists_ell_one_of_L_eq_two_positive_repeated
        (H := H) (r := r) hpos1 hpos2 hpos3 hrep

/-- Exact `ell = 2` part of the complete finite `L=2` Definition 3
classification.

For three source layers, an `ell=2` source datum exists precisely when the
three all-source strict triangle inequalities hold. -/
theorem exists_ell_two_sourceData_iff_triangle_of_L_eq_two
    {H : ℕ → ℕ} {r : ℕ} :
    (∃ C : AoyagiSelectedCutpoints 2,
      AoyagiDefinition3SourceData 2 2 H r C) ↔
      ((2 : ℤ) * aoyagiReducedWidthInt H r 1 <
          aoyagiReducedWidthInt H r 1 + aoyagiReducedWidthInt H r 2 +
            aoyagiReducedWidthInt H r 3 ∧
        (2 : ℤ) * aoyagiReducedWidthInt H r 2 <
          aoyagiReducedWidthInt H r 1 + aoyagiReducedWidthInt H r 2 +
            aoyagiReducedWidthInt H r 3 ∧
        (2 : ℤ) * aoyagiReducedWidthInt H r 3 <
          aoyagiReducedWidthInt H r 1 + aoyagiReducedWidthInt H r 2 +
            aoyagiReducedWidthInt H r 3) := by
  constructor
  · rintro ⟨C, S⟩
    have hC : ∀ j : Fin (2 + 1), C.cut j = j.val + 1 :=
      S.cut_eq_consecutive_of_L_eq_two
    have hsum :
        (∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (C.cut j)) =
          aoyagiReducedWidthInt H r 1 + aoyagiReducedWidthInt H r 2 +
            aoyagiReducedWidthInt H r 3 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_two]
      simp [hC]
      ring
    constructor
    · have hstrict := S.selected_strict (0 : Fin (2 + 1))
      have hcut0 : C.cut (0 : Fin (2 + 1)) = 1 := by
        simpa using hC (0 : Fin (2 + 1))
      rw [hcut0, hsum] at hstrict
      simpa using hstrict
    constructor
    · have hstrict := S.selected_strict (1 : Fin (2 + 1))
      have hcut1 : C.cut (1 : Fin (2 + 1)) = 2 := by
        simpa using hC (1 : Fin (2 + 1))
      rw [hcut1, hsum] at hstrict
      simpa using hstrict
    · have hstrict := S.selected_strict (2 : Fin (2 + 1))
      have hcut2 : C.cut (2 : Fin (2 + 1)) = 3 := by
        simpa using hC (2 : Fin (2 + 1))
      rw [hcut2, hsum] at hstrict
      simpa using hstrict
  · intro htri
    have hstrict :
        ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
          (2 : ℤ) * aoyagiReducedWidthInt H r s <
            ∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1) := by
      intro s hs1 hsL
      have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
      have hsum :
          (∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1)) =
            aoyagiReducedWidthInt H r 1 + aoyagiReducedWidthInt H r 2 +
              aoyagiReducedWidthInt H r 3 := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_two]
        norm_num
        ring
      rcases htri with ⟨htri1, htri2, htri3⟩
      rcases hs with rfl | rfl | rfl
      · rw [hsum]
        exact htri1
      · rw [hsum]
        exact htri2
      · rw [hsum]
        exact htri3
    rcases exists_consecutive_of_all_selected_strict
        (L := 2) (H := H) (r := r) (by norm_num) hstrict with
      ⟨C, _hC, S⟩
    exact ⟨C, S⟩

/-- Complete finite classification of Definition 3 source-data existence for
`L=2`.

Either two source-range reduced-width values repeat and all three values are
positive, realized by `ell=1`, or the three all-source triangle inequalities
hold, realized by `ell=2`. -/
theorem exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two
    {H : ℕ → ℕ} {r : ℕ} :
    (∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
      AoyagiDefinition3SourceData 2 ell H r C) ↔
      (((0 : ℤ) < aoyagiReducedWidthInt H r 1 ∧
        (0 : ℤ) < aoyagiReducedWidthInt H r 2 ∧
        (0 : ℤ) < aoyagiReducedWidthInt H r 3 ∧
        (aoyagiReducedWidthInt H r 1 = aoyagiReducedWidthInt H r 2 ∨
          aoyagiReducedWidthInt H r 1 = aoyagiReducedWidthInt H r 3 ∨
          aoyagiReducedWidthInt H r 2 = aoyagiReducedWidthInt H r 3)) ∨
       ((2 : ℤ) * aoyagiReducedWidthInt H r 1 <
          aoyagiReducedWidthInt H r 1 + aoyagiReducedWidthInt H r 2 +
            aoyagiReducedWidthInt H r 3 ∧
        (2 : ℤ) * aoyagiReducedWidthInt H r 2 <
          aoyagiReducedWidthInt H r 1 + aoyagiReducedWidthInt H r 2 +
            aoyagiReducedWidthInt H r 3 ∧
        (2 : ℤ) * aoyagiReducedWidthInt H r 3 <
          aoyagiReducedWidthInt H r 1 + aoyagiReducedWidthInt H r 2 +
            aoyagiReducedWidthInt H r 3)) := by
  constructor
  · rintro ⟨ell, C, S⟩
    have hell_le : ell ≤ 2 := by
      by_contra hnot
      have hell3 : 3 ≤ ell := by omega
      have h0pos :
          1 ≤ C.cut (⟨0, by omega⟩ : Fin (ell + 1)) := C.pos _
      have h01 :
          C.cut (⟨0, by omega⟩ : Fin (ell + 1)) <
            C.cut (⟨1, by omega⟩ : Fin (ell + 1)) :=
        C.cut_strictMono (by
          change (0 : ℕ) < 1
          norm_num)
      have h12cut :
          C.cut (⟨1, by omega⟩ : Fin (ell + 1)) <
            C.cut (⟨2, by omega⟩ : Fin (ell + 1)) :=
        C.cut_strictMono (by
          change (1 : ℕ) < 2
          norm_num)
      have h23cut :
          C.cut (⟨2, by omega⟩ : Fin (ell + 1)) <
            C.cut (⟨3, by omega⟩ : Fin (ell + 1)) :=
        C.cut_strictMono (by
          change (2 : ℕ) < 3
          norm_num)
      have h3le :
          C.cut (⟨3, by omega⟩ : Fin (ell + 1)) ≤ 3 := by
        simpa using S.cut_le (⟨3, by omega⟩ : Fin (ell + 1))
      omega
    have hell_pos : 0 < ell := S.ell_pos
    interval_cases ell
    · left
      exact
        (exists_ell_one_sourceData_iff_repeatedPositive_of_L_eq_two
          (H := H) (r := r)).mp ⟨C, S⟩
    · right
      exact
        (exists_ell_two_sourceData_iff_triangle_of_L_eq_two
          (H := H) (r := r)).mp ⟨C, S⟩
  · rintro (hrep | htri)
    · rcases hrep with ⟨hpos1, hpos2, hpos3, hrep⟩
      rcases exists_ell_one_of_L_eq_two_positive_repeated
          (H := H) (r := r) hpos1 hpos2 hpos3 hrep with
        ⟨C, S⟩
      exact ⟨1, C, S⟩
    · rcases
        (exists_ell_two_sourceData_iff_triangle_of_L_eq_two
          (H := H) (r := r)).mpr htri with
        ⟨C, S⟩
      exact ⟨2, C, S⟩

/-- For `L=2`, Definition 3 source data forces source-range rank-width.

The proof dispatches through the finite `L=2` classification.  In the
repeated-positive branch positivity is explicit; in the triangle branch, any
two of the three strict inequalities force the remaining reduced width to be
positive. -/
theorem sourceRangeRankWidth_of_L_eq_two_sourceData
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData 2 ell H r C) :
    ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s := by
  have hsource :
      ∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
        AoyagiDefinition3SourceData 2 ell H r C :=
    ⟨ell, C, S⟩
  rcases
      (exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two
        (H := H) (r := r)).mp hsource with hrep | htri
  · rcases hrep with ⟨hpos1, hpos2, hpos3, _hrep⟩
    intro s hs1 hsL
    have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
    have hnonneg : 0 ≤ aoyagiReducedWidthInt H r s := by
      rcases hs with rfl | rfl | rfl
      · exact le_of_lt hpos1
      · exact le_of_lt hpos2
      · exact le_of_lt hpos3
    unfold aoyagiReducedWidthInt at hnonneg
    exact_mod_cast (sub_nonneg.mp hnonneg)
  · rcases htri with ⟨htri1, htri2, htri3⟩
    have hpos1 : 0 < aoyagiReducedWidthInt H r 1 := by omega
    have hpos2 : 0 < aoyagiReducedWidthInt H r 2 := by omega
    have hpos3 : 0 < aoyagiReducedWidthInt H r 3 := by omega
    intro s hs1 hsL
    have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
    have hnonneg : 0 ≤ aoyagiReducedWidthInt H r s := by
      rcases hs with rfl | rfl | rfl
      · exact le_of_lt hpos1
      · exact le_of_lt hpos2
      · exact le_of_lt hpos3
    unfold aoyagiReducedWidthInt at hnonneg
    exact_mod_cast (sub_nonneg.mp hnonneg)

/-- For `L=2`, pairwise distinct source-range reduced widths force any
Definition 3 source-data choice to use `ell=2`.

This removes the separate rank-width input from
`ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct`; `L=2` source data already
implies source-range rank-width. -/
theorem ell_eq_two_of_L_eq_two_pairwiseDistinct
    {ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData 2 ell H r C)
    (h12 : aoyagiReducedWidthInt H r 1 ≠ aoyagiReducedWidthInt H r 2)
    (h13 : aoyagiReducedWidthInt H r 1 ≠ aoyagiReducedWidthInt H r 3)
    (h23 : aoyagiReducedWidthInt H r 2 ≠ aoyagiReducedWidthInt H r 3) :
    ell = 2 :=
  S.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct
    S.sourceRangeRankWidth_of_L_eq_two_sourceData h12 h13 h23

/-- For `L=2` and pairwise distinct source-range reduced widths, existence of
Definition 3 source data is equivalent to the all-source strict selected
inequalities, without a separately supplied source-range rank-width input.

In the source-data direction, rank-width follows from the source datum.  In the
all-source-strict direction, rank-width follows from the strict inequalities. -/
theorem exists_sourceData_iff_allSourceStrict_of_L_eq_two_pairwiseDistinct
    {H : ℕ → ℕ} {r : ℕ}
    (h12 : aoyagiReducedWidthInt H r 1 ≠ aoyagiReducedWidthInt H r 2)
    (h13 : aoyagiReducedWidthInt H r 1 ≠ aoyagiReducedWidthInt H r 3)
    (h23 : aoyagiReducedWidthInt H r 2 ≠ aoyagiReducedWidthInt H r 3) :
    (∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
      AoyagiDefinition3SourceData 2 ell H r C) ↔
      ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
        (2 : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1) := by
  constructor
  · rintro ⟨ell, C, S⟩
    exact
      (exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct
        (H := H) (r := r) S.sourceRangeRankWidth_of_L_eq_two_sourceData
        h12 h13 h23).mp ⟨ell, C, S⟩
  · intro hstrict
    exact
      (exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct
        (H := H) (r := r)
        (sourceRangeRankWidth_of_all_selected_strict
          (L := 2) (H := H) (r := r) (by norm_num) hstrict)
        h12 h13 h23).mpr hstrict

/-- For `L=2`, Definition 3 source-data existence supplies natural witnesses
for the three source-range reduced widths. -/
theorem exists_reducedWidthNatTriple_of_L_eq_two_sourceData
    {H : ℕ → ℕ} {r : ℕ}
    (hsource :
      ∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
        AoyagiDefinition3SourceData 2 ell H r C) :
    ∃ w1 w2 w3 : ℕ,
      aoyagiReducedWidthInt H r 1 = (w1 : ℤ) ∧
      aoyagiReducedWidthInt H r 2 = (w2 : ℤ) ∧
      aoyagiReducedWidthInt H r 3 = (w3 : ℤ) := by
  rcases hsource with ⟨ell, C, S⟩
  have hr := S.sourceRangeRankWidth_of_L_eq_two_sourceData
  refine ⟨H 1 - r, H 2 - r, H 3 - r, ?_, ?_, ?_⟩
  · exact aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le H (hr 1 (by norm_num) (by norm_num))
  · exact aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le H (hr 2 (by norm_num) (by norm_num))
  · exact aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le H (hr 3 (by norm_num) (by norm_num))

/-- For three source layers (`L = 2`), the all-source selected constructor is
controlled by the three strict triangle-type inequalities
`2 w_i < w_1 + w_2 + w_3`.

This packages the source-facing special case used by small examples.  It is
still an all-source constructor, not an arbitrary Definition 3 source-data
classification. -/
theorem exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth
    {H : ℕ → ℕ} {r : ℕ} {w1 w2 w3 : ℤ}
    (hw1 : aoyagiReducedWidthInt H r 1 = w1)
    (hw2 : aoyagiReducedWidthInt H r 2 = w2)
    (hw3 : aoyagiReducedWidthInt H r 3 = w3)
    (htri1 : (2 : ℤ) * w1 < w1 + w2 + w3)
    (htri2 : (2 : ℤ) * w2 < w1 + w2 + w3)
    (htri3 : (2 : ℤ) * w3 < w1 + w2 + w3)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s) :
    ∃ (C : AoyagiSelectedCutpoints 2)
        (m : Fin (2 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 2 m),
      (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData 2 2 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
      (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
      m (0 : Fin (2 + 1)) = w1 ∧
      m (1 : Fin (2 + 1)) = w2 ∧
      m (2 : Fin (2 + 1)) = w3 := by
  have hsum :
      (∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1)) =
        w1 + w2 + w3 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_two]
    norm_num [hw1, hw2, hw3]
    ring
  have hstrict :
      ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
        (2 : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1) := by
    intro s hs1 hsL
    have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases hs with rfl | rfl | rfl
    · rw [hw1, hsum]
      exact htri1
    · rw [hw2, hsum]
      exact htri2
    · rw [hw3, hsum]
      exact htri3
  rcases exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth
      (L := 2) (H := H) (r := r) (by norm_num) hstrict hr with
    ⟨C, m, data, hC, S, hm, hnat, hnonneg, hstrict_m, hle, hnatNonneg⟩
  have hm0 : m (0 : Fin (2 + 1)) = w1 := by
    have hcut0 : C.cut (0 : Fin (2 + 1)) = 1 := by
      simpa using hC (0 : Fin (2 + 1))
    rw [hm, aoyagiSelectedReducedWidths_apply, hcut0, hw1]
  have hm1 : m (1 : Fin (2 + 1)) = w2 := by
    have hcut1 : C.cut (1 : Fin (2 + 1)) = 2 := by
      simpa using hC (1 : Fin (2 + 1))
    rw [hm, aoyagiSelectedReducedWidths_apply, hcut1, hw2]
  have hm2 : m (2 : Fin (2 + 1)) = w3 := by
    have hcut2 : C.cut (2 : Fin (2 + 1)) = 3 := by
      simpa using hC (2 : Fin (2 + 1))
    rw [hm, aoyagiSelectedReducedWidths_apply, hcut2, hw3]
  exact
    ⟨C, m, data, hC, S, hm, hnat, hnonneg, hstrict_m, hle, hnatNonneg,
      hm0, hm1, hm2⟩

/-- Concrete three-width triangle inequalities give the all-source strict
selected inequality for `L=2`. -/
theorem allSourceStrict_of_L_eq_two_triangle_widths
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (htri1 : 2 * w1 < w1 + w2 + w3)
    (htri2 : 2 * w2 < w1 + w2 + w3)
    (htri3 : 2 * w3 < w1 + w2 + w3) :
    ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
      (2 : ℤ) * aoyagiReducedWidthInt H r s <
        ∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1) := by
  have hsum :
      (∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1)) =
        (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_two]
    norm_num [hw1, hw2, hw3]
    ring
  have htri1z : (2 : ℤ) * (w1 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    exact_mod_cast htri1
  have htri2z : (2 : ℤ) * (w2 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    exact_mod_cast htri2
  have htri3z : (2 : ℤ) * (w3 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    exact_mod_cast htri3
  intro s hs1 hsL
  have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hs with rfl | rfl | rfl
  · rw [hw1, hsum]
    exact htri1z
  · rw [hw2, hsum]
    exact htri2z
  · rw [hw3, hsum]
    exact htri3z

/-- Concrete three-width triangle inequalities force source-range rank-width
for `L=2`. -/
theorem sourceRangeRankWidth_of_L_eq_two_triangle_widths
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (htri1 : 2 * w1 < w1 + w2 + w3)
    (htri2 : 2 * w2 < w1 + w2 + w3)
    (htri3 : 2 * w3 < w1 + w2 + w3) :
    ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s :=
  sourceRangeRankWidth_of_all_selected_strict
    (L := 2) (H := H) (r := r) (by norm_num)
    (allSourceStrict_of_L_eq_two_triangle_widths
      (H := H) (r := r) hw1 hw2 hw3 htri1 htri2 htri3)

/-- For three source layers (`L = 2`), concrete triangle inequalities give
the all-source selected constructor without a separately supplied source-range
rank-width hypothesis.

This is only the all-source triangle branch.  It removes the rank-width input
by deriving it from the same triangle inequalities; it is not an arbitrary
Definition 3 source-data classification. -/
theorem exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (htri1 : 2 * w1 < w1 + w2 + w3)
    (htri2 : 2 * w2 < w1 + w2 + w3)
    (htri3 : 2 * w3 < w1 + w2 + w3) :
    ∃ (C : AoyagiSelectedCutpoints 2)
        (m : Fin (2 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 2 m),
      (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData 2 2 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
      (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
      m (0 : Fin (2 + 1)) = (w1 : ℤ) ∧
      m (1 : Fin (2 + 1)) = (w2 : ℤ) ∧
      m (2 : Fin (2 + 1)) = (w3 : ℤ) :=
  exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth
    (H := H) (r := r) (w1 := (w1 : ℤ)) (w2 := (w2 : ℤ)) (w3 := (w3 : ℤ))
    hw1 hw2 hw3
    (by exact_mod_cast htri1)
    (by exact_mod_cast htri2)
    (by exact_mod_cast htri3)
    (sourceRangeRankWidth_of_L_eq_two_triangle_widths
      (H := H) (r := r) hw1 hw2 hw3 htri1 htri2 htri3)

/-- For three source layers (`L = 2`), the all-source triangle branch with a
supplied positive-remainder decomposition gives explicit Theorem 2 finite
formula data.

This is only the all-source triangle branch; the repeated-positive `ell = 1`
branch is intentionally not included. -/
theorem exists_consecutive_three_widths_theorem2Formula_of_triangle_remainder_rankWidth
    {H : ℕ → ℕ} {r w1 w2 w3 ceilPred a : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (htri1 : 2 * w1 < w1 + w2 + w3)
    (htri2 : 2 * w2 < w1 + w2 + w3)
    (htri3 : 2 * w3 < w1 + w2 + w3)
    (ha_pos : 0 < a) (ha_le : a ≤ 2)
    (hsum : w1 + w2 + w3 = 2 * ceilPred + a)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s) :
    ∃ (C : AoyagiSelectedCutpoints 2)
        (m : Fin (2 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 2 m),
      (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData 2 2 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (ceilPred : ℤ) + 1 ∧
      data.aParam = a ∧
      data.theorem2OrderFormula = a * (2 - a) + 1 ∧
      (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
      (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
      m (0 : Fin (2 + 1)) = (w1 : ℤ) ∧
      m (1 : Fin (2 + 1)) = (w2 : ℤ) ∧
      m (2 : Fin (2 + 1)) = (w3 : ℤ) ∧
      aoyagiSelectedWidthPairSum 2 m =
        (w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
          (w2 : ℚ) * (w3 : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
        aoyagiTheorem2RegularTerm 2 H r +
          ((a : ℚ) * ((2 : ℚ) - (a : ℚ))) / 8 -
          (((ceilPred : ℚ) + (a : ℚ) / 2) ^ 2) / 2 +
          (((w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
            (w2 : ℚ) * (w3 : ℚ)) / 2) := by
  classical
  have hsumWidths :
      (∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1)) =
        (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_two]
    norm_num [hw1, hw2, hw3]
    ring
  have htri1z : (2 : ℤ) * (w1 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    exact_mod_cast htri1
  have htri2z : (2 : ℤ) * (w2 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    exact_mod_cast htri2
  have htri3z : (2 : ℤ) * (w3 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    exact_mod_cast htri3
  have hstrictSource :
      ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
        (2 : ℤ) * aoyagiReducedWidthInt H r s <
          ∑ j : Fin (2 + 1), aoyagiReducedWidthInt H r (j.val + 1) := by
    intro s hs1 hsL
    have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases hs with rfl | rfl | rfl
    · rw [hw1, hsumWidths]
      exact htri1z
    · rw [hw2, hsumWidths]
      exact htri2z
    · rw [hw3, hsumWidths]
      exact htri3z
  rcases exists_consecutive_of_all_selected_strict
      (L := 2) (H := H) (r := r) (by norm_num) hstrictSource with
    ⟨C, hC, S⟩
  let m : Fin (2 + 1) → ℤ := aoyagiSelectedReducedWidths H r C
  have hm0 : m (0 : Fin (2 + 1)) = (w1 : ℤ) := by
    have hcut0 : C.cut (0 : Fin (2 + 1)) = 1 := by
      simpa using hC (0 : Fin (2 + 1))
    dsimp [m]
    rw [hcut0, hw1]
  have hm1 : m (1 : Fin (2 + 1)) = (w2 : ℤ) := by
    have hcut1 : C.cut (1 : Fin (2 + 1)) = 2 := by
      simpa using hC (1 : Fin (2 + 1))
    dsimp [m]
    rw [hcut1, hw2]
  have hm2 : m (2 : Fin (2 + 1)) = (w3 : ℤ) := by
    have hcut2 : C.cut (2 : Fin (2 + 1)) = 3 := by
      simpa using hC (2 : Fin (2 + 1))
    dsimp [m]
    rw [hcut2, hw3]
  have hsumz :
      (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) =
        (2 : ℤ) * (ceilPred : ℤ) + (a : ℤ) := by
    exact_mod_cast hsum
  have hsum_m :
      (∑ j : Fin (2 + 1), m j) =
        (2 : ℤ) * (ceilPred : ℤ) + (a : ℤ) := by
    calc
      (∑ j : Fin (2 + 1), m j) = (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_two]
        norm_num [hm0, hm1, hm2]
        ring
      _ = (2 : ℤ) * (ceilPred : ℤ) + (a : ℤ) := hsumz
  let data : AoyagiDefinition3CeilData 2 m :=
    AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder
      2 m (ceilPred : ℤ) a (by norm_num) ha_pos ha_le hsum_m
  have hceil : data.ceilWidth = (ceilPred : ℤ) + 1 := rfl
  have hceilQ : (data.ceilWidth : ℚ) = (ceilPred : ℚ) + 1 := by
    rw [hceil]
    norm_num
  have haParam : data.aParam = a := rfl
  have horder : data.theorem2OrderFormula = a * (2 - a) + 1 := by
    simp [AoyagiDefinition3CeilData.theorem2OrderFormula, haParam]
  have hstrict_m :
      ∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j :=
    S.selected_strict_of_eq_selectedReducedWidths rfl
  have hrSelected : ∀ j : Fin (2 + 1), r ≤ H (C.cut j) :=
    fun j ↦ hr (C.cut j) (C.pos j) (S.cut_le j)
  have hnat : ∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ) := by
    intro j
    exact aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le H r C hrSelected j
  have hnonneg : ∀ j : Fin (2 + 1), 0 ≤ m j := by
    intro j
    exact aoyagiSelectedReducedWidths_nonneg_of_rank_le H r C hrSelected j
  have hle : ∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1 := by
    intro i
    exact data.selectedWidth_le_pred_of_sourceSelectedInequality hstrict_m i
  have hnatNonneg : ∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i := by
    intro i
    exact aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le
      H (r := r) (i := i) C hrSelected
  have hpair :
      aoyagiSelectedWidthPairSum 2 m =
        (w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
          (w2 : ℚ) * (w3 : ℚ) := by
    unfold aoyagiSelectedWidthPairSum
    simp [Fin.sum_univ_three, hm0, hm1, hm2]
  have hlambda :
      aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
        aoyagiTheorem2RegularTerm 2 H r +
          ((a : ℚ) * ((2 : ℚ) - (a : ℚ))) / 8 -
          (((ceilPred : ℚ) + (a : ℚ) / 2) ^ 2) / 2 +
          (((w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
            (w2 : ℚ) * (w3 : ℚ)) / 2) := by
    unfold aoyagiTheorem2Lambda_fromCeilData aoyagiTheorem2Lambda_ceil
    rw [hpair, haParam, hceilQ]
    ring
  refine
    ⟨C, m, data, hC, S, rfl, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
      hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩

/-- Odd-total version of the `L = 2` all-source triangle formula package.

For total selected width `T = w1+w2+w3`, the hypothesis `T % 2 = 1`
constructs the Definition 3 ceiling data with `ceilPred = T/2` and
`aParam = 1`, instead of requiring a supplied positive-remainder
decomposition. -/
theorem exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (htri1 : 2 * w1 < w1 + w2 + w3)
    (htri2 : 2 * w2 < w1 + w2 + w3)
    (htri3 : 2 * w3 < w1 + w2 + w3)
    (hodd : (w1 + w2 + w3) % 2 = 1)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s) :
    ∃ (C : AoyagiSelectedCutpoints 2)
        (m : Fin (2 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 2 m),
      (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData 2 2 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = ((w1 + w2 + w3) / 2 : ℤ) + 1 ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 2 ∧
      (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
      (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
      m (0 : Fin (2 + 1)) = (w1 : ℤ) ∧
      m (1 : Fin (2 + 1)) = (w2 : ℤ) ∧
      m (2 : Fin (2 + 1)) = (w3 : ℤ) ∧
      aoyagiSelectedWidthPairSum 2 m =
        (w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
          (w2 : ℚ) * (w3 : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
        aoyagiTheorem2RegularTerm 2 H r +
          ((1 : ℚ) * ((2 : ℚ) - (1 : ℚ))) / 8 -
          ((((w1 + w2 + w3) / 2 : ℕ) : ℚ) + (1 : ℚ) / 2) ^ 2 / 2 +
          (((w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
            (w2 : ℚ) * (w3 : ℚ)) / 2) := by
  classical
  have hsum : w1 + w2 + w3 = 2 * ((w1 + w2 + w3) / 2) + 1 := by
    omega
  rcases exists_consecutive_three_widths_theorem2Formula_of_triangle_remainder_rankWidth
      (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
      (ceilPred := (w1 + w2 + w3) / 2) (a := 1)
      hw1 hw2 hw3 htri1 htri2 htri3 (by norm_num) (by norm_num) hsum hr with
    ⟨C, m, data, hC, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m,
      hle, hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩
  have horder' : data.theorem2OrderFormula = 2 := by
    simpa using horder
  exact
    ⟨C, m, data, hC, S, hm, hceil, haParam, horder', hnat, hnonneg, hstrict_m,
      hle, hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩

/-- Even-total version of the `L = 2` all-source triangle formula package.

For total selected width `T = w1+w2+w3`, the hypothesis `T % 2 = 0`
constructs the Definition 3 ceiling data with `ceilPred = T/2 - 1` and
`aParam = 2`, instead of requiring a supplied positive-remainder
decomposition. -/
theorem exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (htri1 : 2 * w1 < w1 + w2 + w3)
    (htri2 : 2 * w2 < w1 + w2 + w3)
    (htri3 : 2 * w3 < w1 + w2 + w3)
    (heven : (w1 + w2 + w3) % 2 = 0)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s) :
    ∃ (C : AoyagiSelectedCutpoints 2)
        (m : Fin (2 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 2 m),
      (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData 2 2 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = ((w1 + w2 + w3) / 2 : ℤ) ∧
      data.aParam = 2 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
      (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
      m (0 : Fin (2 + 1)) = (w1 : ℤ) ∧
      m (1 : Fin (2 + 1)) = (w2 : ℤ) ∧
      m (2 : Fin (2 + 1)) = (w3 : ℤ) ∧
      aoyagiSelectedWidthPairSum 2 m =
        (w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
          (w2 : ℚ) * (w3 : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
        aoyagiTheorem2RegularTerm 2 H r +
          ((2 : ℚ) * ((2 : ℚ) - (2 : ℚ))) / 8 -
          ((((w1 + w2 + w3) / 2 - 1 : ℕ) : ℚ) + (2 : ℚ) / 2) ^ 2 / 2 +
          (((w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
            (w2 : ℚ) * (w3 : ℚ)) / 2) := by
  classical
  have hsum :
      w1 + w2 + w3 = 2 * ((w1 + w2 + w3) / 2 - 1) + 2 := by
    omega
  rcases exists_consecutive_three_widths_theorem2Formula_of_triangle_remainder_rankWidth
      (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
      (ceilPred := (w1 + w2 + w3) / 2 - 1) (a := 2)
      hw1 hw2 hw3 htri1 htri2 htri3 (by norm_num) (by norm_num) hsum hr with
    ⟨C, m, data, hC, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m,
      hle, hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩
  have hceil' : data.ceilWidth = ((w1 + w2 + w3) / 2 : ℤ) := by
    rw [hceil]
    have hnat : (w1 + w2 + w3) / 2 - 1 + 1 = (w1 + w2 + w3) / 2 := by
      omega
    exact_mod_cast hnat
  have horder' : data.theorem2OrderFormula = 1 := by
    simpa using horder
  exact
    ⟨C, m, data, hC, S, hm, hceil', haParam, horder', hnat, hnonneg, hstrict_m,
      hle, hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩

/-- Odd-total `L=2` all-source triangle formula package, deriving the
source-range rank-width hypothesis from the concrete triangle inequalities. -/
theorem exists_consecutive_three_widths_theorem2Formula_of_triangle_odd
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (htri1 : 2 * w1 < w1 + w2 + w3)
    (htri2 : 2 * w2 < w1 + w2 + w3)
    (htri3 : 2 * w3 < w1 + w2 + w3)
    (hodd : (w1 + w2 + w3) % 2 = 1) :
    ∃ (C : AoyagiSelectedCutpoints 2)
        (m : Fin (2 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 2 m),
      (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData 2 2 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = ((w1 + w2 + w3) / 2 : ℤ) + 1 ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 2 ∧
      (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
      (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
      m (0 : Fin (2 + 1)) = (w1 : ℤ) ∧
      m (1 : Fin (2 + 1)) = (w2 : ℤ) ∧
      m (2 : Fin (2 + 1)) = (w3 : ℤ) ∧
      aoyagiSelectedWidthPairSum 2 m =
        (w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
          (w2 : ℚ) * (w3 : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
        aoyagiTheorem2RegularTerm 2 H r +
          ((1 : ℚ) * ((2 : ℚ) - (1 : ℚ))) / 8 -
          ((((w1 + w2 + w3) / 2 : ℕ) : ℚ) + (1 : ℚ) / 2) ^ 2 / 2 +
          (((w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
            (w2 : ℚ) * (w3 : ℚ)) / 2) := by
  exact
    exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth
      (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
      hw1 hw2 hw3 htri1 htri2 htri3 hodd
      (sourceRangeRankWidth_of_L_eq_two_triangle_widths
        (H := H) (r := r) hw1 hw2 hw3 htri1 htri2 htri3)

/-- Even-total `L=2` all-source triangle formula package, deriving the
source-range rank-width hypothesis from the concrete triangle inequalities. -/
theorem exists_consecutive_three_widths_theorem2Formula_of_triangle_even
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (htri1 : 2 * w1 < w1 + w2 + w3)
    (htri2 : 2 * w2 < w1 + w2 + w3)
    (htri3 : 2 * w3 < w1 + w2 + w3)
    (heven : (w1 + w2 + w3) % 2 = 0) :
    ∃ (C : AoyagiSelectedCutpoints 2)
        (m : Fin (2 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 2 m),
      (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData 2 2 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = ((w1 + w2 + w3) / 2 : ℤ) ∧
      data.aParam = 2 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
      (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
      m (0 : Fin (2 + 1)) = (w1 : ℤ) ∧
      m (1 : Fin (2 + 1)) = (w2 : ℤ) ∧
      m (2 : Fin (2 + 1)) = (w3 : ℤ) ∧
      aoyagiSelectedWidthPairSum 2 m =
        (w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
          (w2 : ℚ) * (w3 : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
        aoyagiTheorem2RegularTerm 2 H r +
          ((2 : ℚ) * ((2 : ℚ) - (2 : ℚ))) / 8 -
          ((((w1 + w2 + w3) / 2 - 1 : ℕ) : ℚ) + (2 : ℚ) / 2) ^ 2 / 2 +
          (((w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
            (w2 : ℚ) * (w3 : ℚ)) / 2) := by
  exact
    exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth
      (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
      hw1 hw2 hw3 htri1 htri2 htri3 heven
      (sourceRangeRankWidth_of_L_eq_two_triangle_widths
        (H := H) (r := r) hw1 hw2 hw3 htri1 htri2 htri3)

/-- For `L = 2` and an exposed `ell = 1` selected pair, a positive selected
pair cover with a supplied remainder-one decomposition gives explicit Theorem
2 finite formula data.

This is the safe repeated-positive branch interface: the selected pair is part
of the input, so the theorem does not choose a canonical pair from a repeated
width disjunction. -/
theorem exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth
    {H : ℕ → ℕ} {r u v ceilPred : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ 2 + 1)
    (hu : aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (u : ℤ))
    (hv : aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (v : ℤ))
    (hu_pos : 0 < u) (hv_pos : 0 < v)
    (hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
      aoyagiReducedWidthInt H r s ∈
        Finset.univ.image
          (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)))
    (hsum : u + v = ceilPred + 1)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s) :
    ∃ (m : Fin (1 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 1 m),
      AoyagiDefinition3SourceData 2 1 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (ceilPred : ℤ) + 1 ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
      m (0 : Fin (1 + 1)) = (u : ℤ) ∧
      m (1 : Fin (1 + 1)) = (v : ℤ) ∧
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data =
        aoyagiTheorem2RegularTerm 2 H r + ((u : ℚ) * (v : ℚ)) / 2 := by
  classical
  have hu_pos_z :
      0 < aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) := by
    rw [hu]
    exact_mod_cast hu_pos
  have hv_pos_z :
      0 < aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) := by
    rw [hv]
    exact_mod_cast hv_pos
  let S : AoyagiDefinition3SourceData 2 1 H r C :=
    of_ell_eq_one_selectedValueSet_covers
      (L := 2) (H := H) (r := r) (C := C)
      hcut_le hu_pos_z hv_pos_z hcover
  let m : Fin (1 + 1) → ℤ := aoyagiSelectedReducedWidths H r C
  have hm0 : m (0 : Fin (1 + 1)) = (u : ℤ) := by
    dsimp [m]
    rw [hu]
  have hm1 : m (1 : Fin (1 + 1)) = (v : ℤ) := by
    dsimp [m]
    rw [hv]
  have hsumz :
      (u : ℤ) + (v : ℤ) = (ceilPred : ℤ) + (1 : ℤ) := by
    exact_mod_cast hsum
  have hsum_m :
      (∑ j : Fin (1 + 1), m j) =
        (1 : ℤ) * (ceilPred : ℤ) + (1 : ℤ) := by
    calc
      (∑ j : Fin (1 + 1), m j) = (u : ℤ) + (v : ℤ) := by
        rw [Fin.sum_univ_two]
        norm_num [hm0, hm1]
      _ = (1 : ℤ) * (ceilPred : ℤ) + (1 : ℤ) := by
        rw [hsumz]
        ring
  let data : AoyagiDefinition3CeilData 1 m :=
    AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder
      1 m (ceilPred : ℤ) 1 (by norm_num) (by norm_num) (by norm_num) hsum_m
  have hceil : data.ceilWidth = (ceilPred : ℤ) + 1 := rfl
  have haParam : data.aParam = 1 := rfl
  have horder : data.theorem2OrderFormula = 1 := by
    simp [AoyagiDefinition3CeilData.theorem2OrderFormula, haParam]
  have hstrict_m :
      ∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j :=
    S.selected_strict_of_eq_selectedReducedWidths rfl
  have hrSelected : ∀ j : Fin (1 + 1), r ≤ H (C.cut j) :=
    fun j ↦ hr (C.cut j) (C.pos j) (hcut_le j)
  have hnat : ∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ) := by
    intro j
    exact aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le H r C hrSelected j
  have hnonneg : ∀ j : Fin (1 + 1), 0 ≤ m j := by
    intro j
    exact aoyagiSelectedReducedWidths_nonneg_of_rank_le H r C hrSelected j
  have hle : ∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1 := by
    intro i
    exact data.selectedWidth_le_pred_of_sourceSelectedInequality hstrict_m i
  have hnatNonneg : ∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i := by
    intro i
    exact aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le
      H (r := r) (i := i) C hrSelected
  have hpair :
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) := by
    unfold aoyagiSelectedWidthPairSum
    simp [Fin.sum_univ_two, hm0, hm1]
  have hlambda :
      aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data =
        aoyagiTheorem2RegularTerm 2 H r + ((u : ℚ) * (v : ℚ)) / 2 := by
    unfold aoyagiTheorem2Lambda_fromCeilData aoyagiTheorem2Lambda_ceil
    rw [hpair, haParam]
    ring
  exact
    ⟨m, data, S, rfl, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
      hnatNonneg, hm0, hm1, hpair, hlambda⟩

/-- For arbitrary `L` and an exposed `ell = 1` selected pair, a positive
selected-pair cover gives explicit Theorem 2 finite formula data with the
`ell = 1` ceiling datum chosen directly.

The selected pair is part of the input, so this theorem does not choose a
canonical branch from repeated selected values. -/
theorem exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth_general
    {L : ℕ} {H : ℕ → ℕ} {r u v : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ L + 1)
    (hu : aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (u : ℤ))
    (hv : aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (v : ℤ))
    (hu_pos : 0 < u) (hv_pos : 0 < v)
    (hcover : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
      aoyagiReducedWidthInt H r s ∈
        Finset.univ.image
          (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)))
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s) :
    ∃ (m : Fin (1 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 1 m),
      AoyagiDefinition3SourceData L 1 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (u : ℤ) + (v : ℤ) ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
      m (0 : Fin (1 + 1)) = (u : ℤ) ∧
      m (1 : Fin (1 + 1)) = (v : ℤ) ∧
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
        aoyagiTheorem2RegularTerm L H r + ((u : ℚ) * (v : ℚ)) / 2 := by
  classical
  have hu_pos_z :
      0 < aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) := by
    rw [hu]
    exact_mod_cast hu_pos
  have hv_pos_z :
      0 < aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) := by
    rw [hv]
    exact_mod_cast hv_pos
  let S : AoyagiDefinition3SourceData L 1 H r C :=
    of_ell_eq_one_selectedValueSet_covers
      (L := L) (H := H) (r := r) (C := C)
      hcut_le hu_pos_z hv_pos_z hcover
  let m : Fin (1 + 1) → ℤ := aoyagiSelectedReducedWidths H r C
  have hm0 : m (0 : Fin (1 + 1)) = (u : ℤ) := by
    dsimp [m]
    rw [hu]
  have hm1 : m (1 : Fin (1 + 1)) = (v : ℤ) := by
    dsimp [m]
    rw [hv]
  have hsum : u + v = (u + v - 1) + 1 := by
    omega
  have hsumz :
      (u : ℤ) + (v : ℤ) = ((u + v - 1 : ℕ) : ℤ) + (1 : ℤ) := by
    exact_mod_cast hsum
  have hsum_m :
      (∑ j : Fin (1 + 1), m j) =
        (1 : ℤ) * ((u + v - 1 : ℕ) : ℤ) + (1 : ℤ) := by
    calc
      (∑ j : Fin (1 + 1), m j) = (u : ℤ) + (v : ℤ) := by
        rw [Fin.sum_univ_two]
        norm_num [hm0, hm1]
      _ = (1 : ℤ) * ((u + v - 1 : ℕ) : ℤ) + (1 : ℤ) := by
        rw [hsumz]
        ring
  let data : AoyagiDefinition3CeilData 1 m :=
    AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder
      1 m ((u + v - 1 : ℕ) : ℤ) 1 (by norm_num) (by norm_num) (by norm_num)
      hsum_m
  have hceil : data.ceilWidth = ((u + v - 1 : ℕ) : ℤ) + 1 := rfl
  have hceil_uv : data.ceilWidth = (u : ℤ) + (v : ℤ) := by
    rw [hceil]
    have hnat : u + v - 1 + 1 = u + v := by
      omega
    have hz : ((u + v - 1 : ℕ) : ℤ) + 1 = ((u + v : ℕ) : ℤ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_add] using hz
  have haParam : data.aParam = 1 := rfl
  have horder : data.theorem2OrderFormula = 1 := by
    simp [AoyagiDefinition3CeilData.theorem2OrderFormula, haParam]
  have hstrict_m :
      ∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j :=
    S.selected_strict_of_eq_selectedReducedWidths rfl
  have hrSelected : ∀ j : Fin (1 + 1), r ≤ H (C.cut j) :=
    fun j ↦ hr (C.cut j) (C.pos j) (hcut_le j)
  have hnat : ∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ) := by
    intro j
    exact aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le H r C hrSelected j
  have hnonneg : ∀ j : Fin (1 + 1), 0 ≤ m j := by
    intro j
    exact aoyagiSelectedReducedWidths_nonneg_of_rank_le H r C hrSelected j
  have hle : ∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1 := by
    intro i
    exact data.selectedWidth_le_pred_of_sourceSelectedInequality hstrict_m i
  have hnatNonneg : ∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i := by
    intro i
    exact aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le
      H (r := r) (i := i) C hrSelected
  have hpair :
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) := by
    unfold aoyagiSelectedWidthPairSum
    simp [Fin.sum_univ_two, hm0, hm1]
  have hlambda :
      aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
        aoyagiTheorem2RegularTerm L H r + ((u : ℚ) * (v : ℚ)) / 2 := by
    unfold aoyagiTheorem2Lambda_fromCeilData aoyagiTheorem2Lambda_ceil
    rw [hpair, haParam]
    ring
  exact
    ⟨m, data, S, rfl, hceil_uv, haParam, horder, hnat, hnonneg, hstrict_m, hle,
      hnatNonneg, hm0, hm1, hpair, hlambda⟩

/-- A supplied `ell = 1` Definition 3 source datum gives the explicit finite
Theorem 2 formula for its two selected widths.

This theorem removes the separate selected-value cover and positivity inputs
from the exposed selected-pair formula package; `ell = 1` remains supplied. -/
theorem exists_ell_one_theorem2Formula_of_sourceData_rankWidth_general
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (S : AoyagiDefinition3SourceData L 1 H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s) :
    ∃ (u v : ℕ)
        (m : Fin (1 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 1 m),
      u = H (C.cut (0 : Fin (1 + 1))) - r ∧
      v = H (C.cut (1 : Fin (1 + 1))) - r ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (u : ℤ) + (v : ℤ) ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
      m (0 : Fin (1 + 1)) = (u : ℤ) ∧
      m (1 : Fin (1 + 1)) = (v : ℤ) ∧
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
        aoyagiTheorem2RegularTerm L H r + ((u : ℚ) * (v : ℚ)) / 2 := by
  classical
  let u : ℕ := H (C.cut (0 : Fin (1 + 1))) - r
  let v : ℕ := H (C.cut (1 : Fin (1 + 1))) - r
  have hrSelected : ∀ j : Fin (1 + 1), r ≤ H (C.cut j) :=
    fun j ↦ hr (C.cut j) (C.pos j) (S.cut_le j)
  have hu :
      aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (u : ℤ) := by
    dsimp [u]
    exact aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le H
      (hrSelected (0 : Fin (1 + 1)))
  have hv :
      aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (v : ℤ) := by
    dsimp [v]
    exact aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le H
      (hrSelected (1 : Fin (1 + 1)))
  have hu_red_pos :
      0 < aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) := by
    have hstrict := S.selected_strict (1 : Fin (1 + 1))
    rw [Fin.sum_univ_two] at hstrict
    norm_num at hstrict
    omega
  have hv_red_pos :
      0 < aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) := by
    have hstrict := S.selected_strict (0 : Fin (1 + 1))
    rw [Fin.sum_univ_two] at hstrict
    norm_num at hstrict
    omega
  have hu_pos : 0 < u := by
    have hzu : 0 < (u : ℤ) := by
      rwa [hu] at hu_red_pos
    exact_mod_cast hzu
  have hv_pos : 0 < v := by
    have hzv : 0 < (v : ℤ) := by
      rwa [hv] at hv_red_pos
    exact_mod_cast hzv
  have hcover :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        aoyagiReducedWidthInt H r s ∈
          Finset.univ.image
            (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
    intro s hs1 hsL
    exact S.reducedWidth_mem_selectedValueSet_of_ell_eq_one hs1 hsL
  rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth_general
      (L := L) (H := H) (r := r) (u := u) (v := v) (C := C)
      S.cut_le hu hv hu_pos hv_pos hcover hr with
    ⟨m, data, _S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m,
      hle, hnatNonneg, hm0, hm1, hpair, hlambda⟩
  exact
    ⟨u, v, m, data, rfl, rfl, hm, hceil, haParam, horder, hnat, hnonneg,
      hstrict_m, hle, hnatNonneg, hm0, hm1, hpair, hlambda⟩

/-- A supplied `ell = 1` Definition 3 source datum gives the explicit finite
Theorem 2 formula for its two selected widths, without a separate source-range
rank-width hypothesis.

For `ell = 1`, Definition 3 source data itself forces source-range
rank-width; see `sourceRangeRankWidth_of_ell_eq_one`. -/
theorem exists_ell_one_theorem2Formula_of_sourceData_general
    {L : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (S : AoyagiDefinition3SourceData L 1 H r C) :
    ∃ (u v : ℕ)
        (m : Fin (1 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 1 m),
      u = H (C.cut (0 : Fin (1 + 1))) - r ∧
      v = H (C.cut (1 : Fin (1 + 1))) - r ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (u : ℤ) + (v : ℤ) ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
      m (0 : Fin (1 + 1)) = (u : ℤ) ∧
      m (1 : Fin (1 + 1)) = (v : ℤ) ∧
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData L 1 H r m data =
        aoyagiTheorem2RegularTerm L H r + ((u : ℚ) * (v : ℚ)) / 2 :=
  S.exists_ell_one_theorem2Formula_of_sourceData_rankWidth_general
    S.sourceRangeRankWidth_of_ell_eq_one

/-- For `L = 2` and an exposed `ell = 1` selected pair, a positive selected
pair cover gives explicit Theorem 2 finite formula data with the `ell = 1`
ceiling datum chosen directly.

For `ell = 1`, no quotient/remainder input is needed: the selected sum is
`u + v`, so Definition 3 can take `ceilWidth = u + v` and `aParam = 1`. -/
theorem exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth
    {H : ℕ → ℕ} {r u v : ℕ}
    {C : AoyagiSelectedCutpoints 1}
    (hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ 2 + 1)
    (hu : aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (u : ℤ))
    (hv : aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (v : ℤ))
    (hu_pos : 0 < u) (hv_pos : 0 < v)
    (hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
      aoyagiReducedWidthInt H r s ∈
        Finset.univ.image
          (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)))
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s) :
    ∃ (m : Fin (1 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 1 m),
      AoyagiDefinition3SourceData 2 1 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (u : ℤ) + (v : ℤ) ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
      m (0 : Fin (1 + 1)) = (u : ℤ) ∧
      m (1 : Fin (1 + 1)) = (v : ℤ) ∧
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data =
        aoyagiTheorem2RegularTerm 2 H r + ((u : ℚ) * (v : ℚ)) / 2 := by
  classical
  have hsum : u + v = (u + v - 1) + 1 := by omega
  rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth
      (H := H) (r := r) (u := u) (v := v) (ceilPred := u + v - 1) (C := C)
      hcut_le hu hv hu_pos hv_pos hcover hsum hr with
    ⟨m, data, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
      hnatNonneg, hm0, hm1, hpair, hlambda⟩
  have hceil_uv : data.ceilWidth = (u : ℤ) + (v : ℤ) := by
    rw [hceil]
    have hnat : u + v - 1 + 1 = u + v := by omega
    have hz : ((u + v - 1 : ℕ) : ℤ) + 1 = ((u + v : ℕ) : ℤ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_add] using hz
  exact
    ⟨m, data, S, hm, hceil_uv, haParam, horder, hnat, hnonneg, hstrict_m, hle,
      hnatNonneg, hm0, hm1, hpair, hlambda⟩

/-- For `L = 2`, a positive repeated reduced-width profile gives an `ell = 1`
Theorem 2 finite formula package, with the selected pair constructed from the
repeated-equality branch.

The repeated branch is not made canonical: the input disjunction includes the
branch-compatible remainder decomposition for the pair selected in that branch.
This theorem only removes the previously supplied selected pair/cover data. -/
theorem exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_remainder_rankWidth
    {H : ℕ → ℕ} {r w1 w2 w3 ceilPred : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (hw1_pos : 0 < w1) (hw2_pos : 0 < w2) (hw3_pos : 0 < w3)
    (hrep :
      (w1 = w2 ∧ w1 + w3 = ceilPred + 1) ∨
        (w1 = w3 ∧ w1 + w2 = ceilPred + 1) ∨
          (w2 = w3 ∧ w1 + w2 = ceilPred + 1))
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s) :
    ∃ (C : AoyagiSelectedCutpoints 1)
        (u v : ℕ)
        (m : Fin (1 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 1 m),
      0 < u ∧
      0 < v ∧
      u + v = ceilPred + 1 ∧
      AoyagiDefinition3SourceData 2 1 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (ceilPred : ℤ) + 1 ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
      m (0 : Fin (1 + 1)) = (u : ℤ) ∧
      m (1 : Fin (1 + 1)) = (v : ℤ) ∧
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data =
        aoyagiTheorem2RegularTerm 2 H r + ((u : ℚ) * (v : ℚ)) / 2 := by
  classical
  rcases hrep with h12branch | hrest
  · rcases h12branch with ⟨h12, hsum⟩
    let C : AoyagiSelectedCutpoints 1 :=
      { cut := fun j ↦ if j = (0 : Fin (1 + 1)) then 1 else 3
        pos := by
          intro j
          fin_cases j <;> simp
        strict := by
          intro j
          fin_cases j
          simp }
    have hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ 2 + 1 := by
      intro j
      fin_cases j <;> norm_num [C]
    have hu : aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (w1 : ℤ) := by
      simp [C, hw1]
    have hv : aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (w3 : ℤ) := by
      simp [C, hw3]
    have hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
        aoyagiReducedWidthInt H r s ∈
          Finset.univ.image
            (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
      intro s hs1 hsL
      have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
      rcases hs with rfl | rfl | rfl
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C, hw1, hw2, h12]
      · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
    rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth
        (H := H) (r := r) (u := w1) (v := w3) (ceilPred := ceilPred)
        (C := C) hcut_le hu hv hw1_pos hw3_pos hcover hsum hr with
      ⟨m, data, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
        hnatNonneg, hm0, hm1, hpair, hlambda⟩
    exact
      ⟨C, w1, w3, m, data, hw1_pos, hw3_pos, hsum, S, hm, hceil, haParam,
        horder, hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hpair,
        hlambda⟩
  · rcases hrest with h13branch | h23branch
    · rcases h13branch with ⟨h13, hsum⟩
      let C : AoyagiSelectedCutpoints 1 :=
        { cut := fun j ↦ j.val + 1
          pos := by
            intro j
            omega
          strict := by
            intro j
            fin_cases j
            simp }
      have hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ 2 + 1 := by
        intro j
        fin_cases j <;> norm_num [C]
      have hu :
          aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (w1 : ℤ) := by
        simp [C, hw1]
      have hv :
          aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (w2 : ℤ) := by
        simp [C, hw2]
      have hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
          aoyagiReducedWidthInt H r s ∈
            Finset.univ.image
              (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
        intro s hs1 hsL
        have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
        rcases hs with rfl | rfl | rfl
        · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C]
        · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C]
        · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C, hw1, hw3, h13]
      rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth
          (H := H) (r := r) (u := w1) (v := w2) (ceilPred := ceilPred)
          (C := C) hcut_le hu hv hw1_pos hw2_pos hcover hsum hr with
        ⟨m, data, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
          hnatNonneg, hm0, hm1, hpair, hlambda⟩
      exact
        ⟨C, w1, w2, m, data, hw1_pos, hw2_pos, hsum, S, hm, hceil, haParam,
          horder, hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hpair,
          hlambda⟩
    · rcases h23branch with ⟨h23, hsum⟩
      let C : AoyagiSelectedCutpoints 1 :=
        { cut := fun j ↦ j.val + 1
          pos := by
            intro j
            omega
          strict := by
            intro j
            fin_cases j
            simp }
      have hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ 2 + 1 := by
        intro j
        fin_cases j <;> norm_num [C]
      have hu :
          aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (w1 : ℤ) := by
        simp [C, hw1]
      have hv :
          aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (w2 : ℤ) := by
        simp [C, hw2]
      have hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
          aoyagiReducedWidthInt H r s ∈
            Finset.univ.image
              (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
        intro s hs1 hsL
        have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
        rcases hs with rfl | rfl | rfl
        · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C]
        · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C]
        · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C, hw2, hw3, h23]
      rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth
          (H := H) (r := r) (u := w1) (v := w2) (ceilPred := ceilPred)
          (C := C) hcut_le hu hv hw1_pos hw2_pos hcover hsum hr with
        ⟨m, data, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
          hnatNonneg, hm0, hm1, hpair, hlambda⟩
      exact
        ⟨C, w1, w2, m, data, hw1_pos, hw2_pos, hsum, S, hm, hceil, haParam,
          horder, hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hpair,
          hlambda⟩

/-- For `L = 2`, a positive repeated reduced-width profile gives an `ell = 1`
Theorem 2 finite formula package, with the selected pair constructed from the
repeated-equality branch.

This is the preferred repeated-positive interface.  Unlike the compatibility
`..._remainder_rankWidth` version, it does not ask for quotient/remainder data:
for `ell = 1`, the ceiling datum is constructed directly with
`ceilWidth = u + v` and `aParam = 1`. -/
theorem exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_rankWidth
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (hw1_pos : 0 < w1) (hw2_pos : 0 < w2) (hw3_pos : 0 < w3)
    (hrep : w1 = w2 ∨ w1 = w3 ∨ w2 = w3)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → r ≤ H s) :
    ∃ (C : AoyagiSelectedCutpoints 1)
        (u v : ℕ)
        (m : Fin (1 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 1 m),
      0 < u ∧
      0 < v ∧
      AoyagiDefinition3SourceData 2 1 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (u : ℤ) + (v : ℤ) ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
      m (0 : Fin (1 + 1)) = (u : ℤ) ∧
      m (1 : Fin (1 + 1)) = (v : ℤ) ∧
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data =
        aoyagiTheorem2RegularTerm 2 H r + ((u : ℚ) * (v : ℚ)) / 2 := by
  classical
  rcases hrep with h12 | hrest
  · let C : AoyagiSelectedCutpoints 1 :=
      { cut := fun j ↦ if j = (0 : Fin (1 + 1)) then 1 else 3
        pos := by
          intro j
          fin_cases j <;> simp
        strict := by
          intro j
          fin_cases j
          simp }
    have hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ 2 + 1 := by
      intro j
      fin_cases j <;> norm_num [C]
    have hu : aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (w1 : ℤ) := by
      simp [C, hw1]
    have hv : aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (w3 : ℤ) := by
      simp [C, hw3]
    have hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
        aoyagiReducedWidthInt H r s ∈
          Finset.univ.image
            (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
      intro s hs1 hsL
      have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
      rcases hs with rfl | rfl | rfl
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
      · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C, hw1, hw2, h12]
      · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
        simp [C]
    rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth
        (H := H) (r := r) (u := w1) (v := w3) (C := C)
        hcut_le hu hv hw1_pos hw3_pos hcover hr with
      ⟨m, data, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
        hnatNonneg, hm0, hm1, hpair, hlambda⟩
    exact
      ⟨C, w1, w3, m, data, hw1_pos, hw3_pos, S, hm, hceil, haParam, horder,
        hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hpair, hlambda⟩
  · rcases hrest with h13 | h23
    · let C : AoyagiSelectedCutpoints 1 :=
        { cut := fun j ↦ j.val + 1
          pos := by
            intro j
            omega
          strict := by
            intro j
            fin_cases j
            simp }
      have hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ 2 + 1 := by
        intro j
        fin_cases j <;> norm_num [C]
      have hu :
          aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (w1 : ℤ) := by
        simp [C, hw1]
      have hv :
          aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (w2 : ℤ) := by
        simp [C, hw2]
      have hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
          aoyagiReducedWidthInt H r s ∈
            Finset.univ.image
              (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
        intro s hs1 hsL
        have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
        rcases hs with rfl | rfl | rfl
        · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C]
        · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C]
        · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C, hw1, hw3, h13]
      rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth
          (H := H) (r := r) (u := w1) (v := w2) (C := C)
          hcut_le hu hv hw1_pos hw2_pos hcover hr with
        ⟨m, data, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
          hnatNonneg, hm0, hm1, hpair, hlambda⟩
      exact
        ⟨C, w1, w2, m, data, hw1_pos, hw2_pos, S, hm, hceil, haParam, horder,
          hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hpair, hlambda⟩
    · let C : AoyagiSelectedCutpoints 1 :=
        { cut := fun j ↦ j.val + 1
          pos := by
            intro j
            omega
          strict := by
            intro j
            fin_cases j
            simp }
      have hcut_le : ∀ j : Fin (1 + 1), C.cut j ≤ 2 + 1 := by
        intro j
        fin_cases j <;> norm_num [C]
      have hu :
          aoyagiReducedWidthInt H r (C.cut (0 : Fin (1 + 1))) = (w1 : ℤ) := by
        simp [C, hw1]
      have hv :
          aoyagiReducedWidthInt H r (C.cut (1 : Fin (1 + 1))) = (w2 : ℤ) := by
        simp [C, hw2]
      have hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
          aoyagiReducedWidthInt H r s ∈
            Finset.univ.image
              (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H r (C.cut j)) := by
        intro s hs1 hsL
        have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
        rcases hs with rfl | rfl | rfl
        · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C]
        · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C]
        · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
          simp [C, hw2, hw3, h23]
      rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth
          (H := H) (r := r) (u := w1) (v := w2) (C := C)
          hcut_le hu hv hw1_pos hw2_pos hcover hr with
        ⟨m, data, S, hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
          hnatNonneg, hm0, hm1, hpair, hlambda⟩
      exact
        ⟨C, w1, w2, m, data, hw1_pos, hw2_pos, S, hm, hceil, haParam, horder,
          hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hpair, hlambda⟩

/-- For `L = 2`, a positive repeated reduced-width profile gives an `ell = 1`
Theorem 2 finite formula package, deriving source-range rank-width from the
Nat-valued reduced-width identities.

This keeps the repeated branch noncanonical: the returned selected pair depends
on the input repeated-equality disjunction. -/
theorem exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (hw1_pos : 0 < w1) (hw2_pos : 0 < w2) (hw3_pos : 0 < w3)
    (hrep : w1 = w2 ∨ w1 = w3 ∨ w2 = w3) :
    ∃ (C : AoyagiSelectedCutpoints 1)
        (u v : ℕ)
        (m : Fin (1 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 1 m),
      0 < u ∧
      0 < v ∧
      AoyagiDefinition3SourceData 2 1 H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      data.ceilWidth = (u : ℤ) + (v : ℤ) ∧
      data.aParam = 1 ∧
      data.theorem2OrderFormula = 1 ∧
      (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (1 + 1),
        (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
      (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
      m (0 : Fin (1 + 1)) = (u : ℤ) ∧
      m (1 : Fin (1 + 1)) = (v : ℤ) ∧
      aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
      aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data =
        aoyagiTheorem2RegularTerm 2 H r + ((u : ℚ) * (v : ℚ)) / 2 := by
  exact
    exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_rankWidth
      (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
      hw1 hw2 hw3 hw1_pos hw2_pos hw3_pos hrep
      (sourceRangeRankWidth_of_three_reducedWidthInt_eq_natCast hw1 hw2 hw3)

/-- The repeated-positive `L=2`, `ell=1` finite Theorem 2 branch package.

This is a package proposition for dispatch theorems.  It records the branch
tags together with the same conclusion as
`exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated`. -/
def L2RepeatedPositiveTheorem2FormulaBranch
    (H : ℕ → ℕ) (r w1 w2 w3 : ℕ) : Prop :=
  0 < w1 ∧
  0 < w2 ∧
  0 < w3 ∧
  (w1 = w2 ∨ w1 = w3 ∨ w2 = w3) ∧
  ∃ (C : AoyagiSelectedCutpoints 1)
      (u v : ℕ)
      (m : Fin (1 + 1) → ℤ)
      (data : AoyagiDefinition3CeilData 1 m),
    0 < u ∧
    0 < v ∧
    AoyagiDefinition3SourceData 2 1 H r C ∧
    m = aoyagiSelectedReducedWidths H r C ∧
    data.ceilWidth = (u : ℤ) + (v : ℤ) ∧
    data.aParam = 1 ∧
    data.theorem2OrderFormula = 1 ∧
    (∀ j : Fin (1 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
    (∀ j : Fin (1 + 1), 0 ≤ m j) ∧
    (∀ i : Fin (1 + 1),
      (1 : ℤ) * m i < ∑ j : Fin (1 + 1), m j) ∧
    (∀ i : Fin (1 + 1), m i ≤ data.ceilWidth - 1) ∧
    (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 1 m i) ∧
    m (0 : Fin (1 + 1)) = (u : ℤ) ∧
    m (1 : Fin (1 + 1)) = (v : ℤ) ∧
    aoyagiSelectedWidthPairSum 1 m = (u : ℚ) * (v : ℚ) ∧
    aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data =
      aoyagiTheorem2RegularTerm 2 H r + ((u : ℚ) * (v : ℚ)) / 2

/-- The odd-total all-source `L=2`, `ell=2` finite Theorem 2 branch package.

This is a package proposition for dispatch theorems.  It records the triangle
and parity branch tags together with the same conclusion as
`exists_consecutive_three_widths_theorem2Formula_of_triangle_odd`. -/
def L2TriangleOddTheorem2FormulaBranch
    (H : ℕ → ℕ) (r w1 w2 w3 : ℕ) : Prop :=
  2 * w1 < w1 + w2 + w3 ∧
  2 * w2 < w1 + w2 + w3 ∧
  2 * w3 < w1 + w2 + w3 ∧
  (w1 + w2 + w3) % 2 = 1 ∧
  ∃ (C : AoyagiSelectedCutpoints 2)
      (m : Fin (2 + 1) → ℤ)
      (data : AoyagiDefinition3CeilData 2 m),
    (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
    AoyagiDefinition3SourceData 2 2 H r C ∧
    m = aoyagiSelectedReducedWidths H r C ∧
    data.ceilWidth = ((w1 + w2 + w3) / 2 : ℤ) + 1 ∧
    data.aParam = 1 ∧
    data.theorem2OrderFormula = 2 ∧
    (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
    (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
    (∀ i : Fin (2 + 1),
      (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
    (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
    (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
    m (0 : Fin (2 + 1)) = (w1 : ℤ) ∧
    m (1 : Fin (2 + 1)) = (w2 : ℤ) ∧
    m (2 : Fin (2 + 1)) = (w3 : ℤ) ∧
    aoyagiSelectedWidthPairSum 2 m =
      (w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
        (w2 : ℚ) * (w3 : ℚ) ∧
    aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
      aoyagiTheorem2RegularTerm 2 H r +
        ((1 : ℚ) * ((2 : ℚ) - (1 : ℚ))) / 8 -
        ((((w1 + w2 + w3) / 2 : ℕ) : ℚ) + (1 : ℚ) / 2) ^ 2 / 2 +
        (((w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
          (w2 : ℚ) * (w3 : ℚ)) / 2)

/-- The even-total all-source `L=2`, `ell=2` finite Theorem 2 branch package.

This is a package proposition for dispatch theorems.  It records the triangle
and parity branch tags together with the same conclusion as
`exists_consecutive_three_widths_theorem2Formula_of_triangle_even`. -/
def L2TriangleEvenTheorem2FormulaBranch
    (H : ℕ → ℕ) (r w1 w2 w3 : ℕ) : Prop :=
  2 * w1 < w1 + w2 + w3 ∧
  2 * w2 < w1 + w2 + w3 ∧
  2 * w3 < w1 + w2 + w3 ∧
  (w1 + w2 + w3) % 2 = 0 ∧
  ∃ (C : AoyagiSelectedCutpoints 2)
      (m : Fin (2 + 1) → ℤ)
      (data : AoyagiDefinition3CeilData 2 m),
    (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
    AoyagiDefinition3SourceData 2 2 H r C ∧
    m = aoyagiSelectedReducedWidths H r C ∧
    data.ceilWidth = ((w1 + w2 + w3) / 2 : ℤ) ∧
    data.aParam = 2 ∧
    data.theorem2OrderFormula = 1 ∧
    (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
    (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
    (∀ i : Fin (2 + 1),
      (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
    (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
    (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
    m (0 : Fin (2 + 1)) = (w1 : ℤ) ∧
    m (1 : Fin (2 + 1)) = (w2 : ℤ) ∧
    m (2 : Fin (2 + 1)) = (w3 : ℤ) ∧
    aoyagiSelectedWidthPairSum 2 m =
      (w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
        (w2 : ℚ) * (w3 : ℚ) ∧
    aoyagiTheorem2Lambda_fromCeilData 2 2 H r m data =
      aoyagiTheorem2RegularTerm 2 H r +
        ((2 : ℚ) * ((2 : ℚ) - (2 : ℚ))) / 8 -
        ((((w1 + w2 + w3) / 2 - 1 : ℕ) : ℚ) + (2 : ℚ) / 2) ^ 2 / 2 +
        (((w1 : ℚ) * (w2 : ℚ) + (w1 : ℚ) * (w3 : ℚ) +
          (w2 : ℚ) * (w3 : ℚ)) / 2)

/-- Any `L=2` Definition 3 source-data witness yields one of the finite
Theorem 2 branch packages.

This is deliberately a disjunction.  Aoyagi's printed Definition 3/Theorem 2
does not choose a canonical branch, and the branch-overlap diagnostics show
that branch-independent finite lambda/order payloads are unsafe. -/
theorem exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ))
    (hsource :
      ∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
        AoyagiDefinition3SourceData 2 ell H r C) :
    L2RepeatedPositiveTheorem2FormulaBranch H r w1 w2 w3 ∨
      L2TriangleOddTheorem2FormulaBranch H r w1 w2 w3 ∨
        L2TriangleEvenTheorem2FormulaBranch H r w1 w2 w3 := by
  classical
  rcases
      (exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two
        (H := H) (r := r)).mp hsource with hrepInt | htriInt
  · rcases hrepInt with ⟨hw1_pos_z, hw2_pos_z, hw3_pos_z, hrep_z⟩
    have hw1_pos_z' : (0 : ℤ) < (w1 : ℤ) := by
      simpa [hw1] using hw1_pos_z
    have hw2_pos_z' : (0 : ℤ) < (w2 : ℤ) := by
      simpa [hw2] using hw2_pos_z
    have hw3_pos_z' : (0 : ℤ) < (w3 : ℤ) := by
      simpa [hw3] using hw3_pos_z
    have hw1_pos : 0 < w1 := by exact_mod_cast hw1_pos_z'
    have hw2_pos : 0 < w2 := by exact_mod_cast hw2_pos_z'
    have hw3_pos : 0 < w3 := by exact_mod_cast hw3_pos_z'
    have hrep : w1 = w2 ∨ w1 = w3 ∨ w2 = w3 := by
      rcases hrep_z with h12 | h13 | h23
      · left
        have h12z : (w1 : ℤ) = (w2 : ℤ) := by
          simpa [hw1, hw2] using h12
        exact_mod_cast h12z
      · right
        left
        have h13z : (w1 : ℤ) = (w3 : ℤ) := by
          simpa [hw1, hw3] using h13
        exact_mod_cast h13z
      · right
        right
        have h23z : (w2 : ℤ) = (w3 : ℤ) := by
          simpa [hw2, hw3] using h23
        exact_mod_cast h23z
    rcases exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated
        (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
        hw1 hw2 hw3 hw1_pos hw2_pos hw3_pos hrep with
      ⟨C, u, v, m, data, hu_pos, hv_pos, S, hm, hceil, haParam, horder,
        hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hpair, hlambda⟩
    left
    exact
      ⟨hw1_pos, hw2_pos, hw3_pos, hrep, C, u, v, m, data, hu_pos, hv_pos, S,
        hm, hceil, haParam, horder, hnat, hnonneg, hstrict_m, hle,
        hnatNonneg, hm0, hm1, hpair, hlambda⟩
  · rcases htriInt with ⟨htri1_z, htri2_z, htri3_z⟩
    have htri1_z' :
        (2 : ℤ) * (w1 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
      simpa [hw1, hw2, hw3] using htri1_z
    have htri2_z' :
        (2 : ℤ) * (w2 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
      simpa [hw1, hw2, hw3] using htri2_z
    have htri3_z' :
        (2 : ℤ) * (w3 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
      simpa [hw1, hw2, hw3] using htri3_z
    have htri1 : 2 * w1 < w1 + w2 + w3 := by exact_mod_cast htri1_z'
    have htri2 : 2 * w2 < w1 + w2 + w3 := by exact_mod_cast htri2_z'
    have htri3 : 2 * w3 < w1 + w2 + w3 := by exact_mod_cast htri3_z'
    by_cases hodd : (w1 + w2 + w3) % 2 = 1
    · rcases exists_consecutive_three_widths_theorem2Formula_of_triangle_odd
          (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
          hw1 hw2 hw3 htri1 htri2 htri3 hodd with
        ⟨C, m, data, hC, S, hm, hceil, haParam, horder, hnat, hnonneg,
          hstrict_m, hle, hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩
      right
      left
      exact
        ⟨htri1, htri2, htri3, hodd, C, m, data, hC, S, hm, hceil, haParam,
          horder, hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hm2,
          hpair, hlambda⟩
    · have heven : (w1 + w2 + w3) % 2 = 0 := by
        have hlt : (w1 + w2 + w3) % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      rcases exists_consecutive_three_widths_theorem2Formula_of_triangle_even
          (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
          hw1 hw2 hw3 htri1 htri2 htri3 heven with
        ⟨C, m, data, hC, S, hm, hceil, haParam, horder, hnat, hnonneg,
          hstrict_m, hle, hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩
      right
      right
      exact
        ⟨htri1, htri2, htri3, heven, C, m, data, hC, S, hm, hceil, haParam,
          horder, hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1, hm2,
          hpair, hlambda⟩

/-- A fixed `L=2`, `ell=2` Definition 3 source datum dispatches only to the
odd/even all-source triangle finite Theorem 2 branches.

This removes the repeated-positive branch from the conclusion only because
`ell=2` is supplied.  It does not choose between the odd and even triangle
branches except by the parity of the three natural reduced widths. -/
theorem exists_L_eq_two_ell_two_theorem2Formula_triangleBranchDisjunction_of_sourceData
    {H : ℕ → ℕ} {r w1 w2 w3 : ℕ}
    {C : AoyagiSelectedCutpoints 2}
    (S : AoyagiDefinition3SourceData 2 2 H r C)
    (hw1 : aoyagiReducedWidthInt H r 1 = (w1 : ℤ))
    (hw2 : aoyagiReducedWidthInt H r 2 = (w2 : ℤ))
    (hw3 : aoyagiReducedWidthInt H r 3 = (w3 : ℤ)) :
    L2TriangleOddTheorem2FormulaBranch H r w1 w2 w3 ∨
      L2TriangleEvenTheorem2FormulaBranch H r w1 w2 w3 := by
  classical
  rcases
      (exists_ell_two_sourceData_iff_triangle_of_L_eq_two
        (H := H) (r := r)).mp ⟨C, S⟩ with
    ⟨htri1_z, htri2_z, htri3_z⟩
  have htri1_z' :
      (2 : ℤ) * (w1 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    simpa [hw1, hw2, hw3] using htri1_z
  have htri2_z' :
      (2 : ℤ) * (w2 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    simpa [hw1, hw2, hw3] using htri2_z
  have htri3_z' :
      (2 : ℤ) * (w3 : ℤ) < (w1 : ℤ) + (w2 : ℤ) + (w3 : ℤ) := by
    simpa [hw1, hw2, hw3] using htri3_z
  have htri1 : 2 * w1 < w1 + w2 + w3 := by exact_mod_cast htri1_z'
  have htri2 : 2 * w2 < w1 + w2 + w3 := by exact_mod_cast htri2_z'
  have htri3 : 2 * w3 < w1 + w2 + w3 := by exact_mod_cast htri3_z'
  by_cases hodd : (w1 + w2 + w3) % 2 = 1
  · rcases exists_consecutive_three_widths_theorem2Formula_of_triangle_odd
        (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
        hw1 hw2 hw3 htri1 htri2 htri3 hodd with
      ⟨Ctri, m, data, hCtri, Stri, hm, hceil, haParam, horder, hnat, hnonneg,
        hstrict_m, hle, hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩
    left
    exact
      ⟨htri1, htri2, htri3, hodd, Ctri, m, data, hCtri, Stri, hm, hceil,
        haParam, horder, hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1,
        hm2, hpair, hlambda⟩
  · have heven : (w1 + w2 + w3) % 2 = 0 := by
      have hlt : (w1 + w2 + w3) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    rcases exists_consecutive_three_widths_theorem2Formula_of_triangle_even
        (H := H) (r := r) (w1 := w1) (w2 := w2) (w3 := w3)
        hw1 hw2 hw3 htri1 htri2 htri3 heven with
      ⟨Ctri, m, data, hCtri, Stri, hm, hceil, haParam, horder, hnat, hnonneg,
        hstrict_m, hle, hnatNonneg, hm0, hm1, hm2, hpair, hlambda⟩
    right
    exact
      ⟨htri1, htri2, htri3, heven, Ctri, m, data, hCtri, Stri, hm, hceil,
        haParam, horder, hnat, hnonneg, hstrict_m, hle, hnatNonneg, hm0, hm1,
        hm2, hpair, hlambda⟩

/-- A fixed `L=2`, `ell=2` Definition 3 source datum supplies Nat-valued
reduced widths and dispatches only to the odd/even triangle finite Theorem 2
branches. -/
theorem exists_L_eq_two_ell_two_theorem2Formula_triangleBranchDisjunction_of_sourceData_natWidths
    {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints 2}
    (S : AoyagiDefinition3SourceData 2 2 H r C) :
    ∃ w1 w2 w3 : ℕ,
      aoyagiReducedWidthInt H r 1 = (w1 : ℤ) ∧
      aoyagiReducedWidthInt H r 2 = (w2 : ℤ) ∧
      aoyagiReducedWidthInt H r 3 = (w3 : ℤ) ∧
      (L2TriangleOddTheorem2FormulaBranch H r w1 w2 w3 ∨
        L2TriangleEvenTheorem2FormulaBranch H r w1 w2 w3) := by
  rcases exists_reducedWidthNatTriple_of_L_eq_two_sourceData
      ⟨2, C, S⟩ with
    ⟨w1, w2, w3, hw1, hw2, hw3⟩
  exact
    ⟨w1, w2, w3, hw1, hw2, hw3,
      exists_L_eq_two_ell_two_theorem2Formula_triangleBranchDisjunction_of_sourceData
        (H := H) (r := r) (C := C) S hw1 hw2 hw3⟩

/-- Any `L=2` Definition 3 source-data witness supplies Nat-valued reduced
widths and yields the existing finite Theorem 2 branch disjunction.

This theorem deliberately returns a disjunction rather than a branch-independent
formula: Aoyagi's printed Definition 3 does not choose a canonical branch. -/
theorem exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData_natWidths
    {H : ℕ → ℕ} {r : ℕ}
    (hsource :
      ∃ (ell : ℕ) (C : AoyagiSelectedCutpoints ell),
        AoyagiDefinition3SourceData 2 ell H r C) :
    ∃ w1 w2 w3 : ℕ,
      aoyagiReducedWidthInt H r 1 = (w1 : ℤ) ∧
      aoyagiReducedWidthInt H r 2 = (w2 : ℤ) ∧
      aoyagiReducedWidthInt H r 3 = (w3 : ℤ) ∧
      (L2RepeatedPositiveTheorem2FormulaBranch H r w1 w2 w3 ∨
        L2TriangleOddTheorem2FormulaBranch H r w1 w2 w3 ∨
          L2TriangleEvenTheorem2FormulaBranch H r w1 w2 w3) := by
  rcases exists_reducedWidthNatTriple_of_L_eq_two_sourceData hsource with
    ⟨w1, w2, w3, hw1, hw2, hw3⟩
  exact
    ⟨w1, w2, w3, hw1, hw2, hw3,
      exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData
        hw1 hw2 hw3 hsource⟩

/-- Diagnostic: the printed `L = 2` Definition 3 conditions can admit both the
`ell = 1` repeated-positive branch and the `ell = 2` all-source triangle branch
with different finite Theorem 2 lambda formula values.

For reduced widths `(2,3,3)` and `r = 0`, the selected pair `(2,3)` gives
lambda `3`, while the all-source even triangle branch gives lambda `5/2`.
This records finite formula ambiguity only; it is not an analytic RLCT claim. -/
theorem exists_L_eq_two_two_three_three_formula_disagreement :
    let H : ℕ → ℕ :=
      fun s ↦ if s = 1 then 2 else if s = 2 then 3 else if s = 3 then 3 else 0
    ∃ (C1 : AoyagiSelectedCutpoints 1)
        (m1 : Fin (1 + 1) → ℤ)
        (data1 : AoyagiDefinition3CeilData 1 m1)
        (C2 : AoyagiSelectedCutpoints 2)
        (m2 : Fin (2 + 1) → ℤ)
        (data2 : AoyagiDefinition3CeilData 2 m2),
      AoyagiDefinition3SourceData 2 1 H 0 C1 ∧
      m1 = aoyagiSelectedReducedWidths H 0 C1 ∧
      AoyagiDefinition3SourceData 2 2 H 0 C2 ∧
      m2 = aoyagiSelectedReducedWidths H 0 C2 ∧
      aoyagiTheorem2Lambda_fromCeilData 2 1 H 0 m1 data1 = 3 ∧
      aoyagiTheorem2Lambda_fromCeilData 2 2 H 0 m2 data2 = (5 : ℚ) / 2 ∧
      data1.theorem2OrderFormula = 1 ∧
      data2.theorem2OrderFormula = 1 ∧
      aoyagiTheorem2Lambda_fromCeilData 2 1 H 0 m1 data1 ≠
        aoyagiTheorem2Lambda_fromCeilData 2 2 H 0 m2 data2 := by
  classical
  let H : ℕ → ℕ :=
    fun s ↦ if s = 1 then 2 else if s = 2 then 3 else if s = 3 then 3 else 0
  let C1 : AoyagiSelectedCutpoints 1 :=
    { cut := fun j ↦ j.val + 1
      pos := by
        intro j
        omega
      strict := by
        intro j
        fin_cases j
        simp }
  have hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → 0 ≤ H s := by
    intro s _hs1 _hsL
    exact Nat.zero_le (H s)
  have hw1 : aoyagiReducedWidthInt H 0 1 = (2 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  have hw2 : aoyagiReducedWidthInt H 0 2 = (3 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  have hw3 : aoyagiReducedWidthInt H 0 3 = (3 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  have hcut_le : ∀ j : Fin (1 + 1), C1.cut j ≤ 2 + 1 := by
    intro j
    fin_cases j <;> norm_num [C1]
  have hu : aoyagiReducedWidthInt H 0 (C1.cut (0 : Fin (1 + 1))) = (2 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H, C1]
  have hv : aoyagiReducedWidthInt H 0 (C1.cut (1 : Fin (1 + 1))) = (3 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H, C1]
  have hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
      aoyagiReducedWidthInt H 0 s ∈
        Finset.univ.image
          (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H 0 (C1.cut j)) := by
    intro s hs1 hsL
    have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases hs with rfl | rfl | rfl
    · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
      norm_num [aoyagiReducedWidthInt, H, C1]
    · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
      norm_num [aoyagiReducedWidthInt, H, C1]
    · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
      norm_num [aoyagiReducedWidthInt, H, C1]
  rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth
      (H := H) (r := 0) (u := 2) (v := 3) (C := C1)
      hcut_le hu hv (by norm_num) (by norm_num) hcover hr with
    ⟨m1, data1, S1, hm1, _hceil1, _haParam1, horder1, _hnat1, _hnonneg1,
      _hstrict1, _hle1, _hnatNonneg1, _hm10, _hm11, _hpair1, hlambda1⟩
  rcases exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth
      (H := H) (r := 0) (w1 := 2) (w2 := 3) (w3 := 3)
      hw1 hw2 hw3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr with
    ⟨C2, m2, data2, _hC2, S2, hm2, _hceil2, _haParam2, horder2, _hnat2,
      _hnonneg2, _hstrict2, _hle2, _hnatNonneg2, _hm20, _hm21, _hm22, _hpair2,
      hlambda2⟩
  have hlambda1' :
      aoyagiTheorem2Lambda_fromCeilData 2 1 H 0 m1 data1 = 3 := by
    rw [hlambda1]
    norm_num [aoyagiTheorem2RegularTerm, H]
  have hlambda2' :
      aoyagiTheorem2Lambda_fromCeilData 2 2 H 0 m2 data2 = (5 : ℚ) / 2 := by
    rw [hlambda2]
    norm_num [aoyagiTheorem2RegularTerm, H]
  refine
    ⟨C1, m1, data1, C2, m2, data2, S1, hm1, S2, hm2, hlambda1', hlambda2',
      horder1, horder2, ?_⟩
  rw [hlambda1', hlambda2']
  norm_num

/-- Diagnostic: the printed `L = 2` Definition 3 conditions can admit both the
`ell = 1` repeated-positive branch and the `ell = 2` all-source triangle branch
with the same finite Theorem 2 lambda formula value but different finite order
formula values.

For reduced widths `(1,2,2)` and `r = 0`, the selected pair `(1,2)` and the
all-source odd triangle branch both give lambda `1`, while their order formulas
are `1` and `2`.  This records finite formula ambiguity only; it is not an
analytic RLCT or pole-order claim. -/
theorem exists_L_eq_two_one_two_two_order_disagreement :
    let H : ℕ → ℕ :=
      fun s ↦ if s = 1 then 1 else if s = 2 then 2 else if s = 3 then 2 else 0
    ∃ (C1 : AoyagiSelectedCutpoints 1)
        (m1 : Fin (1 + 1) → ℤ)
        (data1 : AoyagiDefinition3CeilData 1 m1)
        (C2 : AoyagiSelectedCutpoints 2)
        (m2 : Fin (2 + 1) → ℤ)
        (data2 : AoyagiDefinition3CeilData 2 m2),
      AoyagiDefinition3SourceData 2 1 H 0 C1 ∧
      m1 = aoyagiSelectedReducedWidths H 0 C1 ∧
      AoyagiDefinition3SourceData 2 2 H 0 C2 ∧
      m2 = aoyagiSelectedReducedWidths H 0 C2 ∧
      aoyagiTheorem2Lambda_fromCeilData 2 1 H 0 m1 data1 = 1 ∧
      aoyagiTheorem2Lambda_fromCeilData 2 2 H 0 m2 data2 = 1 ∧
      data1.theorem2OrderFormula = 1 ∧
      data2.theorem2OrderFormula = 2 ∧
      data1.theorem2OrderFormula ≠ data2.theorem2OrderFormula := by
  classical
  let H : ℕ → ℕ :=
    fun s ↦ if s = 1 then 1 else if s = 2 then 2 else if s = 3 then 2 else 0
  let C1 : AoyagiSelectedCutpoints 1 :=
    { cut := fun j ↦ j.val + 1
      pos := by
        intro j
        omega
      strict := by
        intro j
        fin_cases j
        simp }
  have hr : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 → 0 ≤ H s := by
    intro s _hs1 _hsL
    exact Nat.zero_le (H s)
  have hw1 : aoyagiReducedWidthInt H 0 1 = (1 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  have hw2 : aoyagiReducedWidthInt H 0 2 = (2 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  have hw3 : aoyagiReducedWidthInt H 0 3 = (2 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  have hcut_le : ∀ j : Fin (1 + 1), C1.cut j ≤ 2 + 1 := by
    intro j
    fin_cases j <;> norm_num [C1]
  have hu : aoyagiReducedWidthInt H 0 (C1.cut (0 : Fin (1 + 1))) = (1 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H, C1]
  have hv : aoyagiReducedWidthInt H 0 (C1.cut (1 : Fin (1 + 1))) = (2 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H, C1]
  have hcover : ∀ s : ℕ, 1 ≤ s → s ≤ 2 + 1 →
      aoyagiReducedWidthInt H 0 s ∈
        Finset.univ.image
          (fun j : Fin (1 + 1) ↦ aoyagiReducedWidthInt H 0 (C1.cut j)) := by
    intro s hs1 hsL
    have hs : s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases hs with rfl | rfl | rfl
    · refine Finset.mem_image.mpr ⟨(0 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
      norm_num [aoyagiReducedWidthInt, H, C1]
    · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
      norm_num [aoyagiReducedWidthInt, H, C1]
    · refine Finset.mem_image.mpr ⟨(1 : Fin (1 + 1)), Finset.mem_univ _, ?_⟩
      norm_num [aoyagiReducedWidthInt, H, C1]
  rcases exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth
      (H := H) (r := 0) (u := 1) (v := 2) (C := C1)
      hcut_le hu hv (by norm_num) (by norm_num) hcover hr with
    ⟨m1, data1, S1, hm1, _hceil1, _haParam1, horder1, _hnat1, _hnonneg1,
      _hstrict1, _hle1, _hnatNonneg1, _hm10, _hm11, _hpair1, hlambda1⟩
  rcases exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth
      (H := H) (r := 0) (w1 := 1) (w2 := 2) (w3 := 2)
      hw1 hw2 hw3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr with
    ⟨C2, m2, data2, _hC2, S2, hm2, _hceil2, _haParam2, horder2, _hnat2,
      _hnonneg2, _hstrict2, _hle2, _hnatNonneg2, _hm20, _hm21, _hm22, _hpair2,
      hlambda2⟩
  have hlambda1' :
      aoyagiTheorem2Lambda_fromCeilData 2 1 H 0 m1 data1 = 1 := by
    rw [hlambda1]
    norm_num [aoyagiTheorem2RegularTerm, H]
  have hlambda2' :
      aoyagiTheorem2Lambda_fromCeilData 2 2 H 0 m2 data2 = 1 := by
    rw [hlambda2]
    norm_num [aoyagiTheorem2RegularTerm, H]
  refine
    ⟨C1, m1, data1, C2, m2, data2, S1, hm1, S2, hm2, hlambda1', hlambda2',
      horder1, horder2, ?_⟩
  rw [horder1, horder2]
  norm_num

/-- A concrete nonconstant all-source Definition 3 example.

For `L=2`, `r=0`, and reduced widths `(1,2,2)`, all source layers can be
selected and the selected-width family is nonconstant.  This is only a
diagnostic example; it is not arbitrary source-data existence or a
classification of Definition 3 profiles. -/
theorem exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData :
    let H : ℕ → ℕ :=
      fun s ↦ if s = 1 then 1 else if s = 2 then 2 else if s = 3 then 2 else 0
    ∃ (C : AoyagiSelectedCutpoints 2)
        (m : Fin (2 + 1) → ℤ)
        (data : AoyagiDefinition3CeilData 2 m),
      (∀ j : Fin (2 + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData 2 2 H 0 C ∧
      m = aoyagiSelectedReducedWidths H 0 C ∧
      (∀ j : Fin (2 + 1), m j = ((H (C.cut j) - 0 : ℕ) : ℤ)) ∧
      (∀ j : Fin (2 + 1), 0 ≤ m j) ∧
      (∀ i : Fin (2 + 1),
        (2 : ℤ) * m i < ∑ j : Fin (2 + 1), m j) ∧
      (∀ i : Fin (2 + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat 2 m i) ∧
      m (0 : Fin (2 + 1)) = 1 ∧
      m (1 : Fin (2 + 1)) = 2 ∧
      m (2 : Fin (2 + 1)) = 2 ∧
      m (0 : Fin (2 + 1)) ≠ m (1 : Fin (2 + 1)) := by
  let H : ℕ → ℕ :=
    fun s ↦ if s = 1 then 1 else if s = 2 then 2 else if s = 3 then 2 else 0
  have hw1 : aoyagiReducedWidthInt H 0 1 = (1 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  have hw2 : aoyagiReducedWidthInt H 0 2 = (2 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  have hw3 : aoyagiReducedWidthInt H 0 3 = (2 : ℤ) := by
    norm_num [aoyagiReducedWidthInt, H]
  rcases exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle
      (H := H) (r := 0) (w1 := 1) (w2 := 2) (w3 := 2)
      hw1 hw2 hw3 (by norm_num) (by norm_num) (by norm_num) with
    ⟨C, m, data, hC, S, hm, hnat, hnonneg, hstrict_m, hle, hnatNonneg,
      hm0, hm1, hm2⟩
  refine
    ⟨C, m, data, hC, S, hm, hnat, hnonneg, hstrict_m, hle, hnatNonneg,
      hm0, hm1, hm2, ?_⟩
  rw [hm0, hm1]
  norm_num

/-- Equal-width source data together with the downstream selected reduced-width
ceiling package.

This packages the equal-width example's consecutive cutpoints and derives the
source-range rank-width bound from the same constant reduced-width hypothesis.
It does not compute the ceiling datum in closed form. -/
theorem exists_consecutive_selectedReducedWidthCeilData_of_constant_reducedWidth_pos
    {L : ℕ} {H : ℕ → ℕ} {r w : ℕ}
    (hL : 0 < L) (hw : 0 < w)
    (hconst :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        aoyagiReducedWidthInt H r s = (w : ℤ)) :
    ∃ (C : AoyagiSelectedCutpoints L)
        (m : Fin (L + 1) → ℤ)
        (data : AoyagiDefinition3CeilData L m),
      (∀ j : Fin (L + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData L L H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (L + 1), m j = (w : ℤ)) ∧
      (∀ j : Fin (L + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (L + 1), 0 ≤ m j) ∧
      (∀ i : Fin (L + 1),
        (L : ℤ) * m i < ∑ j : Fin (L + 1), m j) ∧
      (∀ i : Fin (L + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat L m i) := by
  rcases exists_consecutive_of_constant_reducedWidth_pos
      (L := L) (H := H) (r := r) (w := w) hL hw hconst with
    ⟨C, hC, S⟩
  have hr :=
    sourceRangeRankWidth_of_constant_reducedWidth
      (L := L) (H := H) (r := r) (w := w) hconst
  rcases S.exists_selectedReducedWidthCeilData_of_rankWidth hr with
    ⟨m, data, hm, hnat, hnonneg, hstrict, hle, hnatNonneg⟩
  refine ⟨C, m, data, hC, S, hm, ?_, hnat, hnonneg, hstrict, hle, hnatNonneg⟩
  intro j
  rw [hm, aoyagiSelectedReducedWidths_apply]
  exact hconst (C.cut j) (C.pos j) (S.cut_le j)

/-- Equal-width source data with the explicit Definition 3 ceiling datum.

This is the closed-form equal-width lane: if the common reduced width satisfies
`w = L * q + a` with `0 < a <= L`, the selected-width family is constant `w`,
`ceilWidth = w + q + 1`, and `aParam = a`. -/
theorem exists_consecutive_explicitCeilData_of_constant_reducedWidth_decomposition
    {L : ℕ} {H : ℕ → ℕ} {r w q a : ℕ}
    (ha_pos : 0 < a) (ha_le : a ≤ L)
    (hw : w = L * q + a)
    (hconst :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        aoyagiReducedWidthInt H r s = (w : ℤ)) :
    ∃ (C : AoyagiSelectedCutpoints L)
        (m : Fin (L + 1) → ℤ)
        (data : AoyagiDefinition3CeilData L m),
      (∀ j : Fin (L + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData L L H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (L + 1), m j = (w : ℤ)) ∧
      data.ceilWidth = (w : ℤ) + (q : ℤ) + 1 ∧
      data.aParam = a ∧
      (∀ j : Fin (L + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (L + 1), 0 ≤ m j) ∧
      (∀ i : Fin (L + 1),
        (L : ℤ) * m i < ∑ j : Fin (L + 1), m j) ∧
      (∀ i : Fin (L + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat L m i) := by
  classical
  have hL : 0 < L := lt_of_lt_of_le ha_pos ha_le
  have hw_pos : 0 < w := by
    rw [hw]
    omega
  rcases exists_consecutive_of_constant_reducedWidth_pos
      (L := L) (H := H) (r := r) (w := w) hL hw_pos hconst with
    ⟨C, hC, S⟩
  let m : Fin (L + 1) → ℤ := fun _ ↦ (w : ℤ)
  let data : AoyagiDefinition3CeilData L m :=
    AoyagiDefinition3CeilData.equalWidthOfDecomposition L w q a ha_pos ha_le hw
  have hm : m = aoyagiSelectedReducedWidths H r C := by
    funext j
    dsimp [m]
    exact (hconst (C.cut j) (C.pos j) (S.cut_le j)).symm
  have hr :=
    sourceRangeRankWidth_of_constant_reducedWidth
      (L := L) (H := H) (r := r) (w := w) hconst
  have hstrict :
      ∀ i : Fin (L + 1),
        (L : ℤ) * m i < ∑ j : Fin (L + 1), m j :=
    S.selected_strict_of_eq_selectedReducedWidths hm
  refine
    ⟨C, m, data, hC, S, hm, ?_, rfl, rfl, ?_, ?_, hstrict, ?_, ?_⟩
  · intro j
    rfl
  · intro j
    dsimp [m]
    calc
      (w : ℤ) = aoyagiReducedWidthInt H r (C.cut j) :=
        (hconst (C.cut j) (C.pos j) (S.cut_le j)).symm
      _ = ((H (C.cut j) - r : ℕ) : ℤ) :=
        aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le H
          (hr (C.cut j) (C.pos j) (S.cut_le j))
  · intro j
    dsimp [m]
    exact_mod_cast Nat.zero_le w
  · intro i
    exact data.selectedWidth_le_pred_of_sourceSelectedInequality hstrict i
  · intro i
    by_cases hi : i < L + 1
    · rw [aoyagiSelectedWidthNat_of_lt hi]
      dsimp [m]
      exact_mod_cast Nat.zero_le w
    · unfold aoyagiSelectedWidthNat
      simp [hi]

/-- Equal-width source data with explicit finite Theorem 2 formula data.

This extends the equal-width explicit ceiling package by computing the
selected pair sum, order expression, and unfolded finite `lambda` formula for
the constructed consecutive equal-width branch. -/
theorem exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_decomposition
    {L : ℕ} {H : ℕ → ℕ} {r w q a : ℕ}
    (ha_pos : 0 < a) (ha_le : a ≤ L)
    (hw : w = L * q + a)
    (hconst :
      ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 →
        aoyagiReducedWidthInt H r s = (w : ℤ)) :
    ∃ (C : AoyagiSelectedCutpoints L)
        (m : Fin (L + 1) → ℤ)
        (data : AoyagiDefinition3CeilData L m),
      (∀ j : Fin (L + 1), C.cut j = j.val + 1) ∧
      AoyagiDefinition3SourceData L L H r C ∧
      m = aoyagiSelectedReducedWidths H r C ∧
      (∀ j : Fin (L + 1), m j = (w : ℤ)) ∧
      data.ceilWidth = (w : ℤ) + (q : ℤ) + 1 ∧
      data.aParam = a ∧
      data.theorem2OrderFormula = a * (L - a) + 1 ∧
      (∀ j : Fin (L + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (L + 1), 0 ≤ m j) ∧
      (∀ i : Fin (L + 1),
        (L : ℤ) * m i < ∑ j : Fin (L + 1), m j) ∧
      (∀ i : Fin (L + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat L m i) ∧
      aoyagiSelectedWidthPairSum L m =
        (((((L + 1) * L : ℕ) : ℚ) * (w : ℚ)^2) / 2) ∧
      aoyagiTheorem2Lambda_fromCeilData L L H r m data =
        aoyagiTheorem2RegularTerm L H r +
          ((a : ℚ) * ((L : ℚ) - (a : ℚ))) / (4 * (L : ℚ)) -
          (((L : ℚ) * ((L : ℚ) - 1)) / 4) *
            (((w : ℚ) + (q : ℚ) + 1) +
              (((a : ℚ) - (L : ℚ)) / (L : ℚ))) ^ 2 +
          (((((L + 1) * L : ℕ) : ℚ) * (w : ℚ)^2) / 4) := by
  rcases exists_consecutive_explicitCeilData_of_constant_reducedWidth_decomposition
      (L := L) (H := H) (r := r) (w := w) (q := q) (a := a)
      ha_pos ha_le hw hconst with
    ⟨C, m, data, hC, S, hm, hmconst, hceil, haParam, hnat, hnonneg, hstrict,
      hle, hnatNonneg⟩
  have horder : data.theorem2OrderFormula = a * (L - a) + 1 := by
    simp [AoyagiDefinition3CeilData.theorem2OrderFormula, haParam]
  have hm_const_fun : m = fun _ : Fin (L + 1) ↦ (w : ℤ) := by
    funext j
    exact hmconst j
  have hpair :
      aoyagiSelectedWidthPairSum L m =
        (((((L + 1) * L : ℕ) : ℚ) * (w : ℚ)^2) / 2) := by
    rw [hm_const_fun]
    exact aoyagiSelectedWidthPairSum_const L w
  have hlambda :
      aoyagiTheorem2Lambda_fromCeilData L L H r m data =
        aoyagiTheorem2RegularTerm L H r +
          ((a : ℚ) * ((L : ℚ) - (a : ℚ))) / (4 * (L : ℚ)) -
          (((L : ℚ) * ((L : ℚ) - 1)) / 4) *
            (((w : ℚ) + (q : ℚ) + 1) +
              (((a : ℚ) - (L : ℚ)) / (L : ℚ))) ^ 2 +
          (((((L + 1) * L : ℕ) : ℚ) * (w : ℚ)^2) / 4) := by
    unfold aoyagiTheorem2Lambda_fromCeilData aoyagiTheorem2Lambda_ceil
    rw [hpair, hceil, haParam]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring_nf
  exact
    ⟨C, m, data, hC, S, hm, hmconst, hceil, haParam, horder, hnat, hnonneg,
      hstrict, hle, hnatNonneg, hpair, hlambda⟩

end AoyagiDefinition3SourceData

end Aoyagi
end DLN
end DLNFibre
