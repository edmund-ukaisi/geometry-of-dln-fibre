import DLNFibre.DLN.Aoyagi.RegularVariableShift
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly

/-!
# Rank-width handoff for the regular-variable shifted Theorem 2 socket

This file composes Definition 3 source-data provenance with the finite
regular-variable shift using only the source-range rank-width hypothesis.
It keeps the reduced finite minimum/order obligations and shifted extraction
hypothesis explicit.

It does not construct regular-suspension charts, transport analytic ideals,
prove Aoyagi Lemma 1, construct normal-crossing charts, prove active-ratio or
chart-count bounds, or prove pole order/RLCT beyond the explicitly supplied
normal-crossing extraction hypothesis.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

namespace AoyagiDefinition3SourceData

/-- Definition 3 source data plus source-range rank-width hypotheses produce
the final-boundary socket for a finite exponent datum shifted by Aoyagi's
regular block-entry count.

The rank-width hypothesis is used both for the selected-width side data and
for the endpoint bounds in the finite regular-variable shift.  The reduced
finite minimum/order obligations remain supplied. -/
theorem exists_theorem2SuppliedFinalBoundary_of_rankWidth_regularVariableCountShift
    {D : AoyagiNormalCrossingExponentData}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC :
      AoyagiNormalCrossingExtractionHypothesis
        (D.jacobianPriorLossShift
          (aoyagiTheorem2RegularVariableCount L H r))
        lambda poleOrder)
    (hminimum :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          D.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
            aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          D.exponentOrder = data.theorem2OrderFormula) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedFinalBoundary
          (D.jacobianPriorLossShift
            (aoyagiTheorem2RegularVariableCount L H r))
          L ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedFinalBoundary_of_rankWidth hr hNC
    (fun data hselected ↦
      AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift_rankWidth
        data hr (hminimum data hselected) (horder data hselected))

/-- Chart-certificate version of
`exists_theorem2SuppliedFinalBoundary_of_rankWidth_regularVariableCountShift`.

The shifted chart certificate and its extraction hypothesis remain supplied;
this theorem only composes source-range rank-width provenance and finite
exponent-array arithmetic. -/
theorem exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_regularVariableCountShift
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {C : AoyagiSelectedCutpoints ell}
    (S : AoyagiDefinition3SourceData L ell H r C)
    (hr : ∀ s : ℕ, 1 ≤ s → s ≤ L + 1 → r ≤ H s)
    {lambda : ℚ} {poleOrder : ℕ}
    (hNC :
      (Cnc.jacobianPriorLossShift
        (aoyagiTheorem2RegularVariableCount L H r)).ExtractionHypothesis
        lambda poleOrder)
    (hminimum :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cnc.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r =
            aoyagiTheorem2Lambda_fromCeilData L ell H r m data)
    (horder :
      ∀ {m : Fin (ell + 1) → ℤ}
        (data : AoyagiDefinition3CeilData ell m),
        m = aoyagiSelectedReducedWidths H r C →
          Cnc.exponentData.exponentOrder = data.theorem2OrderFormula) :
    ∃ (m : Fin (ell + 1) → ℤ) (data : AoyagiDefinition3CeilData ell m),
      AoyagiTheorem2SuppliedChartFinalBoundary
          (Cnc.jacobianPriorLossShift
            (aoyagiTheorem2RegularVariableCount L H r))
          L ell H r C m data lambda poleOrder ∧
      (∀ j : Fin (ell + 1), m j = ((H (C.cut j) - r : ℕ) : ℤ)) ∧
      (∀ j : Fin (ell + 1), 0 ≤ m j) ∧
      (∀ i : Fin (ell + 1),
        (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      (∀ i : Fin (ell + 1), m i ≤ data.ceilWidth - 1) ∧
      (∀ i : ℕ, 0 ≤ aoyagiSelectedWidthNat ell m i) :=
  S.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth hr hNC
    (fun data hselected ↦
      AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift_rankWidth
        data hr (hminimum data hselected) (horder data hselected))

end AoyagiDefinition3SourceData

end Aoyagi
end DLN
end DLNFibre
