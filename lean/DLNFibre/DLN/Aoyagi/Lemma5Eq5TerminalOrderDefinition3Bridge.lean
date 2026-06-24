import DLNFibre.DLN.Aoyagi.Definition3Bridge
import DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderBridge

/-!
# Definition 3 source-data bridge for Eq5 terminal-order `hsource`

This file removes a duplicated strict selected-width hypothesis from one Eq5
terminal-order route.  The strict inequality is already part of
`AoyagiDefinition3SourceData`; after rewriting the selected-width family by
`m = aoyagiSelectedReducedWidths H r C`, it is exactly the `hsource` consumed by
the existing Eq5 terminal-order cardinal-squeeze theorem.

The bridge leaves Eq5 endpoint-family construction, actual-width/block
dominance, injectivity, and terminal-family payloads explicit.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

open AoyagiLemma5SuppliedNonbaseFamily

set_option linter.style.longLine false

/-- Definition 3 source data supplies the strict selected-width inequality
needed by the Eq5 endpoint-family block-width cardinal squeeze.

All Eq5 source-realisation data, including the blockwise actual-width
hypothesis, remains explicit. -/
theorem
  terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze_of_definition3SourceData
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints (N + 1)}
    {m : Fin (N + 2) → ℤ}
    (Ssrc : AoyagiDefinition3SourceData L (N + 1) H r C)
    (hm : m = aoyagiSelectedReducedWidths H r C)
    (data : AoyagiDefinition3CeilData (N + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N data.aParam data.ceilWidth m t numerator leastValue)
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) data.aParam (pOf label) (labelAlphaOf label)
        data.ceilWidth m C (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      C.block (pOf label) label.1)
    (hactual :
      ∀ i : Fin (N + 1), ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          aoyagiSelectedWidthNat (N + 1) m i.val ≤ (width r : ℤ))
    (hlabelFormula : ∀ label ∈ TC.terminalMinimumLabels,
      (label.2 : ℤ) =
        aoyagiHtildeUpperNat (N + 1) data.aParam data.ceilWidth m
            (pOf label) + 1 -
          (labelAlphaOf label : ℤ))
    (hlabel_ne_base : ∀ label ∈ TC.terminalMinimumLabels,
      T label label.1 ≠ TC.family.baseValue (pOf label))
    (hpAlpha_inj :
      Set.InjOn
        (fun label : Σ _ : ℕ, ℕ ↦
          (Sigma.mk (pOf label) (labelAlphaOf label) : Σ _ : ℕ, ℕ))
        ↑TC.terminalMinimumLabels)
    (baseValue_mem :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        baseValue j ∈
          aoyagiHtildeIntervalValueSetNat
            (N + 1) data.aParam data.ceilWidth m j)
    (halpha_image :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        (strictBranches j).image alphaOf =
          aoyagiLemma5Eq5AlphaDomain (N + 1) data.aParam j)
    (hvalue :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j,
          value b =
            aoyagiHtildeUpperNat (N + 1) data.aParam data.ceilWidth m j -
              (alphaOf b : ℤ))
    (hupper :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        value (upper j) =
          aoyagiHtildeUpperNat (N + 1) data.aParam data.ceilWidth m j)
    (hlower :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ data.aParam →
        j ≤ (N + 1) - data.aParam →
          value (lower j) =
            aoyagiHtildeLowerNat (N + 1) data.aParam data.ceilWidth m j)
    (halpha_inj :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        Set.InjOn alphaOf ↑(strictBranches j))
    (branchCoord : β → ℕ)
    (hstrictCoord :
      ∀ {j : ℕ}, (hj : j ∈ Finset.Icc 1 ((N + 1) - 1)) →
        ∀ b ∈ strictBranches j, branchCoord b = j)
    (hupperCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) →
        branchCoord (upper j) = j)
    (hlowerCoord :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 ((N + 1) - 1) → j ≤ data.aParam →
        j ≤ (N + 1) - data.aParam → branchCoord (lower j) = j)
    (hfamily :
      TC.family.toAoyagiLemma5SuppliedNonbaseFamily =
        ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
          (ell := N + 1) (a := data.aParam) (M := data.ceilWidth) (m := m)
          strictBranches alphaOf value upper lower baseValue data.aParam_le
          baseValue_mem halpha_image hvalue hupper hlower halpha_inj
          branchCoord hstrictCoord hupperCoord hlowerCoord)
    (hbranchS :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.branchS (some b) = C.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (C.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.terminalMinimumLabels.card = data.theorem2OrderFormula :=
  TC.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
    data C pOf labelAlphaOf layerWidth T strictBranches alphaOf value upper
    lower baseValue (Ssrc.selected_strict_of_eq_selectedReducedWidths hm) hT
    hlabelBlock Ssrc.lastPoint_le hactual hlabelFormula hlabel_ne_base hpAlpha_inj
    baseValue_mem halpha_image hvalue hupper hlower halpha_inj branchCoord
    hstrictCoord hupperCoord hlowerCoord hfamily hbranchS hbranchK hbaseLabel

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
