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

/-- Build the finite exponent formula boundary when the minimum is certified
by a supplied active ratio and the order is certified by a supplied chart count
equal to the terminal-minimum label count.

This is finite max/min bookkeeping only; it does not construct charts,
active-ratio bounds, chart-count bounds, Lemma 5 no-extra coverage, pole
order, or RLCT extraction. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card
    data hp hratio hleRatio
    (D.exponentOrder_eq_of_chart_minCount_eq_of_forall_le hchart hleChart)
    hinj hupper

/-- Build the finite exponent formula boundary from source-facing chart counts
at the displayed Theorem 2 ratio, after the active-ratio certificate identifies
that ratio with `D.exponentMinimum`. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card
    data hp hratio hleRatio
    (D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
      (D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
        hp hratio hleRatio)
      hchart hleChart)
    hinj hupper

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

/-- Build the supplied final Theorem 2 boundary from active-ratio and chart
count finite certificates routed through supplied Lemma 5 terminal labels. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card
      data hp hratio hleRatio hchart hleChart hinj hupper

/-- Build the supplied final Theorem 2 boundary from active-ratio and
displayed-ratio chart-count finite certificates. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card
      data hp hratio hleRatio hchart hleChart hinj hupper

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

/-- Pair-form final consequence of active-ratio and chart-count finite
certificates routed through the supplied Lemma 5 terminal-order bridge. -/
theorem lambda_and_poleOrder_eq_of_activePair_chartCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    (TC.theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card
      data hselected hNC hp hratio hleRatio hchart hleChart hinj hupper)
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form final consequence from active-ratio and displayed-ratio
chart-count finite certificates. -/
theorem lambda_and_poleOrder_eq_of_activePair_ratioCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    (TC.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card
      data hselected hNC hp hratio hleRatio hchart hleChart hinj hupper)
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Counted-datum classifier variant of
`theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card`.

This is only a finite handoff wrapper: the counted-datum classifier and
branch-label injectivity remain supplied. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_of_classifier
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
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card
    data hminimum horder hinj
    (TC.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier
      data classifier)

/-- Counted-datum classifier variant of the active-ratio terminal-order
finite exponent bridge. -/
theorem
  theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier
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
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card
    data hp hratio hleRatio horder hinj
    (TC.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier
      data classifier)

/-- Counted-datum classifier variant of the active-ratio/chart-count finite
exponent bridge. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier
    data hp hratio hleRatio
    (D.exponentOrder_eq_of_chart_minCount_eq_of_forall_le hchart hleChart)
    hinj classifier

/-- Counted-datum classifier variant of the active-ratio/displayed-ratio
chart-count finite exponent bridge. -/
theorem theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L (n + 1) H r m data :=
  TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier
    data hp hratio hleRatio
    (D.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
      (D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
        hp hratio hleRatio)
      hchart hleChart)
    hinj classifier

/-- Counted-datum classifier variant of the supplied final boundary with a
raw exponent-minimum formula and terminal-label order equality. -/
theorem theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card_of_classifier
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
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_of_classifier
      data hminimum horder hinj classifier

/-- Counted-datum classifier variant of the supplied final boundary with an
active-ratio minimum certificate. -/
theorem
  theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card_of_classifier
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
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier
      data TC hp hratio hleRatio horder hinj classifier

/-- Counted-datum classifier variant of the active-ratio/chart-count supplied
final boundary. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_chartCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_classifier
      data hp hratio hleRatio hchart hleChart hinj classifier

/-- Counted-datum classifier variant of the active-ratio/displayed-ratio
chart-count supplied final boundary. -/
theorem theorem2SuppliedFinalBoundary_of_activePair_ratioCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
      lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier
      data hp hratio hleRatio hchart hleChart hinj classifier

/-- Pair-form counted-datum classifier consequence in ceiling-data notation. -/
theorem
  lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card_of_classifier
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
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    (TC.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card_of_classifier
      data hselected hNC hminimum horder hinj classifier)
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form counted-datum classifier consequence from an active-ratio
minimum certificate. -/
theorem lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card_of_classifier
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
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    (TC.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card_of_classifier
      data hselected hNC hp hratio hleRatio horder hinj classifier)
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form counted-datum classifier consequence from active-ratio and
chart-count finite certificates. -/
theorem lambda_and_poleOrder_eq_of_activePair_chartCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    (TC.theorem2SuppliedFinalBoundary_of_activePair_chartCount_classifier
      data hselected hNC hp hratio hleRatio hchart hleChart hinj classifier)
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form counted-datum classifier consequence from active-ratio and
displayed-ratio chart-count finite certificates. -/
theorem lambda_and_poleOrder_eq_of_activePair_ratioCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedFinalBoundary D L (n + 1) H r C m data
        lambda poleOrder :=
    (TC.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_classifier
      data hselected hNC hp hratio hleRatio hchart hleChart hinj classifier)
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Chart-certificate final boundary from active-ratio and chart-count
finite certificates routed through supplied Lemma 5 terminal labels. -/
theorem
  theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L (n + 1) H r C m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card
      data hp hratio hleRatio hchart hleChart hinj hupper

/-- Chart-certificate final boundary from active-ratio and displayed-ratio
chart-count certificates routed through supplied Lemma 5 terminal labels. -/
theorem
  theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L (n + 1) H r C m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card
      data hp hratio hleRatio hchart hleChart hinj hupper

/-- Counted-datum classifier variant of the chart-certificate final boundary
with active-ratio and chart-count finite certificates. -/
theorem theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L (n + 1) H r C m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_classifier
      data hp hratio hleRatio hchart hleChart hinj classifier

/-- Counted-datum classifier variant of the chart-certificate final boundary
with active-ratio and displayed-ratio chart-count finite certificates. -/
theorem theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc L (n + 1) H r C m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier
      data hp hratio hleRatio hchart hleChart hinj classifier

/-- Pair-form chart-certificate consequence from active-ratio and chart-count
certificates routed through supplied Lemma 5 terminal labels. -/
theorem lambda_and_poleOrder_eq_of_chart_activePair_chartCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L (n + 1) H r C m data lambda poleOrder :=
    TC.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card
      data hselected hNC hp hratio hleRatio hchart hleChart hinj hupper
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form chart-certificate consequence from active-ratio and
displayed-ratio chart-count certificates routed through supplied Lemma 5
terminal labels. -/
theorem lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_terminalMinimumLabels_card
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (hupper : TC.terminalMinimumLabels.card ≤ data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L (n + 1) H r C m data lambda poleOrder :=
    TC.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card
      data hselected hNC hp hratio hleRatio hchart hleChart hinj hupper
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form counted-datum classifier consequence from active-ratio and
chart-count certificates, preserving the chart certificate. -/
theorem lambda_and_poleOrder_eq_of_chart_activePair_chartCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L (n + 1) H r C m data lambda poleOrder :=
    TC.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_classifier
      data hselected hNC hp hratio hleRatio hchart hleChart hinj classifier
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

/-- Pair-form counted-datum classifier consequence from active-ratio and
displayed-ratio chart-count certificates, preserving the chart certificate. -/
theorem lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_classifier
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
    (hinj : Set.InjOn TC.branchLabel ↑TC.fullBranches)
    (classifier : TC.TerminalMinimumCountDatumClassifier) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let B :
      AoyagiTheorem2SuppliedChartFinalBoundary
        Cnc L (n + 1) H r C m data lambda poleOrder :=
    TC.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_classifier
      data hselected hNC hp hratio hleRatio hchart hleChart hinj classifier
  exact B.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula

end AoyagiLemma5SuppliedTerminalCandidateFamily

namespace AoyagiDefinition3SourceData

set_option linter.style.longLine false

/-- Definition 3 source data plus rank-width hypotheses produce the
selected-width family and ceiling datum consumed by the supplied terminal
counted-datum classifier final-boundary bridge.

The counted-datum classifier, branch-label injectivity, active-ratio
certificate, displayed-ratio chart-count certificate, and A0 extraction
hypothesis remain supplied for the produced `m,data`. -/
theorem
  exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier
    {β : Type*} [DecidableEq β]
    {D : AoyagiNormalCrossingExponentData}
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints (n + 1)}
    (Ssrc : AoyagiDefinition3SourceData L (n + 1) H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hPayload :
      ∀ {m : Fin (n + 2) → ℤ}
        (data : AoyagiDefinition3CeilData (n + 1) m),
        m = aoyagiSelectedReducedWidths H r C →
          ∃ (t : ℕ → ℕ → ℕ → ℤ)
            (numerator leastValue : ℕ → ℕ → ℤ)
            (TC :
              AoyagiLemma5SuppliedTerminalCandidateFamily β L width
                Sfinal Jfinal n data.aParam data.ceilWidth m t numerator
                leastValue)
            (_classifier : TC.TerminalMinimumCountDatumClassifier),
            Set.InjOn TC.branchLabel ↑TC.fullBranches ∧
              ∃ p : Fin D.numCharts × Fin D.numCoords,
                p ∈ D.activePairs ∧
                  D.ratioAt p =
                    aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
                  (∀ p' ∈ D.activePairs,
                    aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
                      D.ratioAt p') ∧
                  ∃ c : Fin D.numCharts,
                    D.countInChartAtRatio
                        (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
                      TC.terminalMinimumLabels.card ∧
                    ∀ c' : Fin D.numCharts,
                      D.countInChartAtRatio
                          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
                        TC.terminalMinimumLabels.card) :
    ∃ (m : Fin (n + 2) → ℤ)
      (data : AoyagiDefinition3CeilData (n + 1) m),
      AoyagiTheorem2SuppliedFinalBoundary
          D L (n + 1) H r C m data lambda poleOrder ∧
      (∀ j : Fin (n + 2), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (n + 2), 0 ≤ m j) ∧
      (∀ i : Fin (n + 2),
        ((n + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (n + 2), m j) ∧
      (∀ i : Fin (n + 2), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat (n + 1) m i) :=
  Ssrc.exists_theorem2SuppliedFinalBoundary_of_rankWidth hr hNC
    (fun data hm => by
      rcases hPayload data hm with
        ⟨t, numerator, leastValue, TC, classifier, hinj, p, hp, hratio,
          hleRatio, c, hchart, hleChart⟩
      exact
        TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier
          data hp hratio hleRatio hchart hleChart hinj classifier)

/-- Chart-certificate version of the Definition 3 terminal counted-datum
classifier final-boundary handoff.

This packages Definition 3 source-data provenance before invoking the supplied
terminal counted-datum classifier bridge for the produced `m,data`. -/
theorem
  exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier
    {Param R : Type*} [CommMonoid R]
    {β : Type*} [DecidableEq β]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L : ℕ} {width : ℕ → ℕ} {Sfinal Jfinal n : ℕ}
    {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints (n + 1)}
    (Ssrc : AoyagiDefinition3SourceData L (n + 1) H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    (hPayload :
      ∀ {m : Fin (n + 2) → ℤ}
        (data : AoyagiDefinition3CeilData (n + 1) m),
        m = aoyagiSelectedReducedWidths H r C →
          ∃ (t : ℕ → ℕ → ℕ → ℤ)
            (numerator leastValue : ℕ → ℕ → ℤ)
            (TC :
              AoyagiLemma5SuppliedTerminalCandidateFamily β L width
                Sfinal Jfinal n data.aParam data.ceilWidth m t numerator
                leastValue)
            (_classifier : TC.TerminalMinimumCountDatumClassifier),
            Set.InjOn TC.branchLabel ↑TC.fullBranches ∧
              ∃ p : Fin Cnc.numCharts × Fin Cnc.numCoords,
                p ∈ Cnc.exponentData.activePairs ∧
                  Cnc.exponentData.ratioAt p =
                    aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ∧
                  (∀ p' ∈ Cnc.exponentData.activePairs,
                    aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data ≤
                      Cnc.exponentData.ratioAt p') ∧
                  ∃ c : Fin Cnc.numCharts,
                    Cnc.exponentData.countInChartAtRatio
                        (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c =
                      TC.terminalMinimumLabels.card ∧
                    ∀ c' : Fin Cnc.numCharts,
                      Cnc.exponentData.countInChartAtRatio
                          (aoyagiTheorem2Lambda_fromCeilData L (n + 1) H r m data) c' ≤
                        TC.terminalMinimumLabels.card) :
    ∃ (m : Fin (n + 2) → ℤ)
      (data : AoyagiDefinition3CeilData (n + 1) m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          Cnc L (n + 1) H r C m data lambda poleOrder ∧
      (∀ j : Fin (n + 2), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (n + 2), 0 ≤ m j) ∧
      (∀ i : Fin (n + 2),
        ((n + 1 : ℕ) : ℤ) * m i < ∑ j : Fin (n + 2), m j) ∧
      (∀ i : Fin (n + 2), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat (n + 1) m i) :=
  Ssrc.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth hr hNC
    (fun data hm => by
      rcases hPayload data hm with
        ⟨t, numerator, leastValue, TC, classifier, hinj, p, hp, hratio,
          hleRatio, c, hchart, hleChart⟩
      exact
        TC.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier
          data hp hratio hleRatio hchart hleChart hinj classifier)

set_option linter.style.longLine true

end AoyagiDefinition3SourceData

end Aoyagi
end DLN
end DLNFibre
