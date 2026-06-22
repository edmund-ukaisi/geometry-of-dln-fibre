import DLNFibre.DLN.Aoyagi.NormalCrossingInterface
import DLNFibre.DLN.Aoyagi.FinalFormula

/-!
# Conditional finite exponent bridge for Aoyagi Theorem 2's displayed formula

This file only composes explicit hypotheses.  It does not prove source
parameter provenance, Definition 3 selected-cutpoint inequalities or
existence, rank-width hypotheses, chart coverage, unit factors,
Jacobian/prior exponent correctness, terminal-minimum exactness, the Lemma 5
order count, or the analytic normal-crossing extraction theorem.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Supplied finite exponent formula equalities needed to read
normal-crossing exponent data as Aoyagi Theorem 2's displayed arithmetic.

This is a boundary structure: it packages finite equalities to be supplied by
the future normal-crossing certificate, not a construction of that certificate. -/
structure AoyagiTheorem2FiniteExponentFormulaHypothesis
    (D : AoyagiNormalCrossingExponentData)
    (L ell : ℕ) (H : ℕ → ℕ) (r : ℕ) (m : Fin (ell + 1) → ℤ)
    (data : AoyagiDefinition3CeilData ell m) : Prop where
  exponentMinimum_eq_theorem2Lambda_fromCeilData :
    D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData L ell H r m data
  exponentOrder_eq_theorem2OrderFormula :
    D.exponentOrder = data.theorem2OrderFormula

namespace AoyagiTheorem2FiniteExponentFormulaHypothesis

/-- Build the finite exponent formula boundary from supplied finite
normal-crossing min/order certificates.

This consumes an active coordinate realizing the displayed `lambda` formula, a
global active-ratio lower bound, a chart realizing the displayed order formula,
and a uniform chart-count upper bound.  It does not construct the exponent
data, prove chart production, or invoke the analytic extraction theorem. -/
theorem of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hp : p ∈ D.activePairs)
    (hratio :
      D.ratioAt p = aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L ell H r m data ≤ D.ratioAt p')
    {c : Fin D.numCharts}
    (hchart : D.minCountInChart c = data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.minCountInChart c' ≤ data.theorem2OrderFormula) :
    AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data where
  exponentMinimum_eq_theorem2Lambda_fromCeilData :=
    D.exponentMinimum_eq_of_activePair_ratioAt_eq_of_forall_le
      hp hratio hleRatio
  exponentOrder_eq_theorem2OrderFormula :=
    D.exponentOrder_eq_of_chart_minCount_eq_of_forall_le hchart hleChart

/-- Conditional consequence of the explicit normal-crossing extraction
hypothesis and supplied finite exponent formula equalities, in ceiling-data
form. -/
theorem lambda_eq_theorem2Lambda_fromCeilData_of_extractionHypothesis
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data := by
  calc
    lambda = D.exponentMinimum := hNC.lambda_eq_exponentMinimum
    _ = aoyagiTheorem2Lambda_fromCeilData L ell H r m data :=
      hFormula.exponentMinimum_eq_theorem2Lambda_fromCeilData

/-- Conditional consequence of the explicit normal-crossing extraction
hypothesis and supplied finite exponent formula equalities, in average form. -/
theorem lambda_eq_theorem2Lambda_average_of_extractionHypothesis
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data) :
    lambda = aoyagiTheorem2Lambda_average L ell H r data.aParam m := by
  calc
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data :=
      hFormula.lambda_eq_theorem2Lambda_fromCeilData_of_extractionHypothesis hNC
    _ = aoyagiTheorem2Lambda_average L ell H r data.aParam m :=
      (aoyagiTheorem2Lambda_average_eq_fromCeilData L ell H r m data).symm

/-- Conditional consequence of the explicit normal-crossing extraction
hypothesis and supplied finite exponent formula equalities, in expanded form. -/
theorem lambda_eq_theorem2Lambda_expanded_of_extractionHypothesis
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data) :
    lambda =
      aoyagiTheorem2Lambda_expanded L ell H r data.aParam data.ceilWidth m := by
  calc
    lambda = aoyagiTheorem2Lambda_average L ell H r data.aParam m :=
      hFormula.lambda_eq_theorem2Lambda_average_of_extractionHypothesis hNC
    _ = aoyagiTheorem2Lambda_expanded L ell H r data.aParam data.ceilWidth m :=
      aoyagiTheorem2Lambda_average_eq_expanded_ofCeilData L ell H r m data

/-- Conditional consequence of the explicit normal-crossing extraction
hypothesis and supplied finite exponent formula equalities, for the extracted
order parameter. -/
theorem poleOrder_eq_theorem2OrderFormula_of_extractionHypothesis
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data) :
    poleOrder = data.theorem2OrderFormula := by
  calc
    poleOrder = D.exponentOrder := hNC.theta_eq_exponentOrder
    _ = data.theorem2OrderFormula := hFormula.exponentOrder_eq_theorem2OrderFormula

/-- Pair form of the conditional finite exponent bridge. -/
theorem lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_extractionHypothesis
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m} {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    (hFormula :
      AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  exact
    ⟨hFormula.lambda_eq_theorem2Lambda_fromCeilData_of_extractionHypothesis hNC,
      hFormula.poleOrder_eq_theorem2OrderFormula_of_extractionHypothesis hNC⟩

/-- Pair form after the supplied finite normal-crossing min/order certificates
and the explicit A0 extraction hypothesis are supplied. -/
theorem lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m) {lambda : ℚ} {poleOrder : ℕ}
    (hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder)
    {p : Fin D.numCharts × Fin D.numCoords}
    (hp : p ∈ D.activePairs)
    (hratio :
      D.ratioAt p = aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (hleRatio : ∀ p' ∈ D.activePairs,
      aoyagiTheorem2Lambda_fromCeilData L ell H r m data ≤ D.ratioAt p')
    {c : Fin D.numCharts}
    (hchart : D.minCountInChart c = data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin D.numCharts,
      D.minCountInChart c' ≤ data.theorem2OrderFormula) :
    lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data ∧
      poleOrder = data.theorem2OrderFormula := by
  let hFormula :
      AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data :=
    of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
      data hp hratio hleRatio hchart hleChart
  exact
    lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_extractionHypothesis
      hNC hFormula

end AoyagiTheorem2FiniteExponentFormulaHypothesis

end Aoyagi
end DLN
end DLNFibre
