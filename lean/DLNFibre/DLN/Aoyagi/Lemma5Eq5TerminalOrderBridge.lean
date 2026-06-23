import DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalClassifier
import DLNFibre.DLN.Aoyagi.FinalFormula

/-!
# Lemma 5 Eq5 terminal order bridge

This file specializes the supplied Eq5 endpoint-family terminal-count theorem
to Aoyagi Definition 3's final order notation.  It is only a finite
bookkeeping bridge: the Eq5 endpoint family, terminal source vectors,
blockwise width dominance, endpoint-family equality, and injectivity payloads
remain explicit hypotheses.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

open AoyagiLemma5SuppliedNonbaseFamily

set_option linter.style.longLine false

/-- The supplied Eq5 endpoint-family block-width cardinal squeeze, rewritten in
Aoyagi Theorem 2's displayed order formula.

All source-realisation and no-extra-coverage content remains in the explicit
Eq5 payload hypotheses.  This theorem only substitutes Definition 3's
`aParam` and `ceilWidth` for the Eq5 parameters and unfolds
`data.theorem2OrderFormula`. -/
theorem
  terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal : ℕ}
    {N : ℕ} {m : Fin (N + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (N + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC : AoyagiLemma5SuppliedTerminalCandidateFamily β L width Sfinal Jfinal
      N data.aParam data.ceilWidth m t numerator leastValue)
    (cut : AoyagiSelectedCutpoints (N + 1))
    (pOf labelAlphaOf : (Σ _ : ℕ, ℕ) → ℕ)
    (layerWidth : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (T : (Σ _ : ℕ, ℕ) → ℕ → ℤ)
    (strictBranches : ℕ → Finset β) (alphaOf : β → ℕ)
    (value : β → ℤ) (upper lower : ℕ → β) (baseValue : ℕ → ℤ)
    (hsource : ∀ i : Fin (N + 2),
      ((N + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (N + 2), m j)
    (hT : ∀ label ∈ TC.terminalMinimumLabels,
      AoyagiLemma5Eq5PiecewiseSourceVector
        (N + 1) data.aParam (pOf label) (labelAlphaOf label)
        data.ceilWidth m cut (layerWidth label) (T label))
    (hlabelBlock : ∀ label ∈ TC.terminalMinimumLabels,
      cut.block (pOf label) label.1)
    (hlast : cut.point (N + 1) ≤ L + 1)
    (hactual :
      ∀ i : Fin (N + 1), ∀ r : ℕ,
        cut.point i.val ≤ r → r < cut.point (i.val + 1) →
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
        TC.branchS (some b) = cut.point (branchCoord b) - 1)
    (hbranchK :
      ∀ j ∈ Finset.Icc 1 N, ∀ b ∈ TC.family.branches j,
        TC.family.value b = (TC.branchK (some b) : ℤ) - 1)
    (hbaseLabel :
      TC.branchLabel none =
        ((Sigma.mk (cut.point (N + 1) - 1) 1) : Σ _ : ℕ, ℕ)) :
    TC.terminalMinimumLabels.card = data.theorem2OrderFormula := by
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using
    (TC.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
      data.aParam_le cut pOf labelAlphaOf layerWidth T strictBranches
      alphaOf value upper lower baseValue data.selectedSum_eq hsource hT
      hlabelBlock hlast hactual hlabelFormula hlabel_ne_base hpAlpha_inj
      baseValue_mem halpha_image hvalue hupper hlower halpha_inj
      branchCoord hstrictCoord hupperCoord hlowerCoord hfamily hbranchS
      hbranchK hbaseLabel)

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
