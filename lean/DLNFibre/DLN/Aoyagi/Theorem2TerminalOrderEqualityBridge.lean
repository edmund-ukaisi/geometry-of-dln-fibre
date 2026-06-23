import DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly

/-!
# Theorem 2 terminal-order equality bridge

This file routes an already-proved exact terminal-minimum count

`TC.terminalMinimumLabels.card = data.theorem2OrderFormula`

into the finite and final Theorem 2 sockets.  It deliberately does not say how
that equality was obtained: it may come from a supplied classifier, from a
supplied Eq5 endpoint-family payload, or from a future source-backed Lemma 5
construction.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

set_option linter.style.longLine false

/-- Build the finite exponent formula boundary from an exact terminal-minimum
order equality.

The exponent-minimum formula and the chart/order equality are still supplied.
This theorem only composes the supplied chart/order equality with the exact
terminal count. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_eq
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
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data where
  exponentMinimum_eq_theorem2Lambda_fromCeilData := hminimum
  exponentOrder_eq_theorem2OrderFormula := horder.trans hterminal

/-- Active-ratio variant of the exact-terminal-count finite exponent bridge. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_eq
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
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_eq
    data
    (D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
      hp hratio hleRatio)
    horder hterminal

/-- Active-ratio and chart-count variant of the exact-terminal-count finite
exponent bridge. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card_eq
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
    {c : Fin D.numCharts}
    (hchart : D.minCountInChart c = TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.minCountInChart c' ≤ TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_eq
    data hp hratio hleRatio
    (D.exponentOrder_eq_of_chart_minCount_eq_of_forall_le hchart hleChart)
    hterminal

/-- Active-ratio and displayed-ratio chart-count variant of the exact-terminal
finite exponent bridge. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card_eq
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
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_eq
    data hp hratio hleRatio
    (D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
      (D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
        hp hratio hleRatio)
      hchart hleChart)
    hterminal

/-- Build the supplied final boundary from a raw exponent-minimum formula,
chart/order equality, and exact terminal count. -/
theorem theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card_eq
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
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_eq
      data hminimum horder hterminal

/-- Supplied final boundary from an active-ratio certificate and exact terminal
count. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card_eq
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
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_eq
      data hp hratio hleRatio horder hterminal

/-- Supplied final boundary from active-ratio and chart-count finite
certificates plus exact terminal count. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card_eq
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
    {c : Fin D.numCharts}
    (hchart : D.minCountInChart c = TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.minCountInChart c' ≤ TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card_eq
      data hp hratio hleRatio hchart hleChart hterminal

/-- Supplied final boundary from active-ratio and displayed-ratio chart-count
finite certificates plus exact terminal count. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card_eq
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
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card_eq
      data hp hratio hleRatio hchart hleChart hterminal

/-- Pair-form final consequence from a raw exponent-minimum formula,
chart/order equality, and exact terminal count. -/
theorem lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card_eq
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
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    TC.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card_eq
      data hselected hNC hminimum horder hterminal
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form final consequence from an active-ratio certificate and exact
terminal count. -/
theorem lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card_eq
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
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    TC.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card_eq
      data hselected hNC hp hratio hleRatio horder hterminal
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form final consequence from active-ratio and chart-count certificates
plus exact terminal count. -/
theorem lambda_and_poleOrder_eq_of_activePair_chartCount_terminalMinimumLabels_card_eq
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
    {c : Fin D.numCharts}
    (hchart : D.minCountInChart c = TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.minCountInChart c' ≤ TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    TC.theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card_eq
      data hselected hNC hp hratio hleRatio hchart hleChart hterminal
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form final consequence from active-ratio and displayed-ratio
chart-count certificates plus exact terminal count. -/
theorem lambda_and_poleOrder_eq_of_activePair_ratioCount_terminalMinimumLabels_card_eq
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
    {c : Fin D.numCharts}
    (hchart :
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    TC.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card_eq
      data hselected hNC hp hratio hleRatio hchart hleChart hterminal
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Chart-certificate final boundary from active-ratio and chart-count
certificates plus exact terminal count. -/
theorem
  theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card_eq
    {Param R : Type*} [CommMonoid R]
    {β : Type*} [DecidableEq β]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
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
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.minCountInChart c = TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.minCountInChart c' ≤ TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L (n + 1) H r C m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card_eq
      data hp hratio hleRatio hchart hleChart hterminal

/-- Chart-certificate final boundary from active-ratio and displayed-ratio
chart-count certificates plus exact terminal count. -/
theorem
  theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card_eq
    {Param R : Type*} [CommMonoid R]
    {β : Type*} [DecidableEq β]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
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
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L (n + 1) H r C m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card_eq
      data hp hratio hleRatio hchart hleChart hterminal

/-- Pair-form chart-certificate consequence from active-ratio and chart-count
certificates plus exact terminal count. -/
theorem lambda_and_poleOrder_eq_of_chart_activePair_chartCount_terminalMinimumLabels_card_eq
    {Param R : Type*} [CommMonoid R]
    {β : Type*} [DecidableEq β]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
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
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.minCountInChart c = TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.minCountInChart c' ≤ TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L (n + 1) H r C m data lambda poleOrder :=
    TC.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card_eq
      data hselected hNC hp hratio hleRatio hchart hleChart hterminal
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form chart-certificate consequence from active-ratio and
displayed-ratio chart-count certificates plus exact terminal count. -/
theorem lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_terminalMinimumLabels_card_eq
    {Param R : Type*} [CommMonoid R]
    {β : Type*} [DecidableEq β]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
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
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (hp : p ∈ Cnc.exponentData.activePairs)
    (hratio :
      Cnc.exponentData.ratioAt p =
        aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
        TC.terminalMinimumLabels.card)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.countInChartAtRatio
          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
        TC.terminalMinimumLabels.card)
    (hterminal :
      TC.terminalMinimumLabels.card = data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L (n + 1) H r C m data lambda poleOrder :=
    TC.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card_eq
      data hselected hNC hp hratio hleRatio hchart hleChart hterminal
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
