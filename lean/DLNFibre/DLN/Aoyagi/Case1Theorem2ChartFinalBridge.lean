import DLNFibre.DLN.Aoyagi.Case1Theorem2FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly

/-!
# Case 1 bridge to the chart-final Theorem 2 boundary

This file composes the selected-old Case 1 finite exponent bridge with the
supplied chart-final boundary for Aoyagi Theorem 2.  It does not construct
normal-crossing charts, prove chart coverage, prove active-ratio lower bounds,
prove chart-count facts, or invoke the analytic extraction theorem beyond the
explicit chart-level extraction hypothesis supplied as an input.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace Case1SelectedOldUnitA0ExponentCoordinateBridge

set_option linter.style.longLine false

/-- Build the supplied chart-final Theorem 2 boundary from a selected-old Case
1 coordinate and chart counts at the Case 1 candidate ratio.

This is only composition of supplied finite and chart-level boundary data.  It
does not construct the selected-old chart boundary, the chart certificate, or
the analytic extraction hypothesis. -/
theorem theorem2SuppliedChartFinalBoundary_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
    {Rsrc : Type*} [CommRing Rsrc]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J J1 s0 k0 : ℕ}
    {level : ℕ → ℕ → ℕ}
    {t t' : ℕ → ℕ → ℕ → ℤ}
    {numerator numerator' leastValue leastValue' : ℕ → ℕ → ℤ}
    {pre post : IntroducedLabelRecurrenceState Lcase n S J Rsrc}
    {u : Rsrc} {baseStep : ℕ → Rsrc}
    {ChartRegular : Case1CenterGenerator → Prop}
    {TransitionRegular : Case1CenterGenerator → Case1CenterGenerator → Prop}
    {cert :
      Case1SelectedOldUnitSuppliedChartFamilyBoundary Rsrc Lcase n S J J1 s0 k0 level
        t t' numerator numerator' leastValue leastValue'
        pre post u baseStep ChartRegular TransitionRegular}
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (B : Case1SelectedOldUnitA0ExponentCoordinateBridge cert Cnc.exponentData p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    {lambda : ℚ} {poleOrder : ℕ}
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    (hcandidate :
      theorem2CandidateRatio n S J J1 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      theorem2CandidateRatio n S J J1 ≤ Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.countInChartAtRatio
          (theorem2CandidateRatio n S J J1) c =
        data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.countInChartAtRatio
          (theorem2CandidateRatio n S J J1) c' ≤
        data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc Lthm ell H r cuts m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    B.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
      data hcandidate hleRatio hchart hleChart

end Case1SelectedOldUnitA0ExponentCoordinateBridge

end Aoyagi
end DLN
end DLNFibre
