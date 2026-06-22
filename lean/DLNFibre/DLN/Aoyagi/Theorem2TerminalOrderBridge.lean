import DLNFibre.DLN.Aoyagi.Lemma5TerminalOrderBridge
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly

/-!
# Theorem 2 terminal-order bridge

This file decomposes the order-count field of the supplied Theorem 2 finite
exponent boundary through the supplied Lemma 5 terminal-minimum interface.

The exponent minimum formula and the equality between the normal-crossing
chart order and the terminal-minimum label count remain supplied.  The only
new step is the finite transitivity from the supplied Lemma 5 obstruction to
`data.theorem2OrderFormula`.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

/-- Build the finite exponent formula boundary when the order count is routed
through the supplied Lemma 5 terminal-minimum labels.

This does not prove the exponent minimum formula, normal-crossing chart
production, the chart-order/terminal-label equality, Lemma 5 no-extra
coverage, pole order, or RLCT extraction. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hminimum :
      D.exponentMinimum =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (horder :
      D.exponentOrder = TC.terminalMinimumLabels.card)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data where
  exponentMinimum_eq_theorem2Lambda_fromCeilData := hminimum
  exponentOrder_eq_theorem2OrderFormula := by
    exact horder.trans
      (TC.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn
        data hinj hupper)

/-- Build the finite exponent formula boundary when the minimum is certified
by a supplied active ratio and the order count is routed through supplied
Lemma 5 terminal-minimum labels.

This does not prove normal-crossing chart production, active-ratio lower
bounds, chart-order/terminal-label equality, Lemma 5 no-extra coverage, pole
order, or RLCT extraction. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hp : p ∈ D.activePairs)
    (hratio :
      D.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        D.ratioAt p')
    (horder :
      D.exponentOrder = TC.terminalMinimumLabels.card)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card
    data
    (D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
      hp hratio hleRatio)
    horder hinj hupper

/-- Build the supplied final Theorem 2 boundary with its order field routed
through the supplied Lemma 5 terminal-minimum labels.

The selected-width provenance, A0 extraction hypothesis, exponent-minimum
formula, and chart-order/terminal-label equality are still explicit supplied
inputs. -/
theorem theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints (n + 1)}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {lambda : ℚ} {poleOrder : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hselected : m = aoyagiSelectedReducedWidths H r C)
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hminimum :
      D.exponentMinimum =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (horder :
      D.exponentOrder = TC.terminalMinimumLabels.card)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card
      data hminimum horder hinj hupper

/-- Build the supplied final Theorem 2 boundary from an active-ratio minimum
certificate and the supplied Lemma 5 terminal-minimum order route.

The selected-width provenance, A0 extraction hypothesis,
chart-order/terminal-label equality, branch-label injectivity, and terminal
upper bound remain explicit supplied inputs. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints (n + 1)}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {lambda : ℚ} {poleOrder : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hselected : m = aoyagiSelectedReducedWidths H r C)
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hp : p ∈ D.activePairs)
    (hratio :
      D.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        D.ratioAt p')
    (horder :
      D.exponentOrder = TC.terminalMinimumLabels.card)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card
      data hp hratio hleRatio horder hinj hupper

/-- Pair-form final consequence of the supplied terminal-order bridge, in
ceiling-data notation. -/
theorem lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints (n + 1)}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {lambda : ℚ} {poleOrder : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hselected : m = aoyagiSelectedReducedWidths H r C)
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hminimum :
      D.exponentMinimum =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (horder :
      D.exponentOrder = TC.terminalMinimumLabels.card)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    (TC.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card
      data hselected hNC hminimum horder hinj hupper)
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form final consequence of the active-ratio minimum certificate plus
the supplied Lemma 5 terminal-order bridge. -/
theorem lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {S J n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints (n + 1)}
    {m : Fin (n + 2) → ℤ}
    (data : AoyagiDefinition3CeilData (n + 1) m)
    {lambda : ℚ} {poleOrder : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (TC :
      AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J
        n data.aParam data.ceilWidth m t numerator leastValue)
    (hselected : m = aoyagiSelectedReducedWidths H r C)
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hp : p ∈ D.activePairs)
    (hratio :
      D.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        D.ratioAt p')
    (horder :
      D.exponentOrder = TC.terminalMinimumLabels.card)
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    (TC.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card
      data hselected hNC hp hratio hleRatio horder hinj hupper)
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
