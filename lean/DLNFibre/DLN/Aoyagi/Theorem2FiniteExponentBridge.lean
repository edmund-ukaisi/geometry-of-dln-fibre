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

end AoyagiTheorem2FiniteExponentFormulaHypothesis

end Aoyagi
end DLN
end DLNFibre
