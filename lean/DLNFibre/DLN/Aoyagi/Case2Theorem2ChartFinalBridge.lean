import DLNFibre.DLN.Aoyagi.Case2Theorem2FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly

/-!
# Case 2 bridge to the chart-final Theorem 2 boundary

This file composes the displayed continuing Case 2 finite exponent bridge with
the supplied chart-final boundary for Aoyagi Theorem 2.  It does not construct
normal-crossing charts, prove chart coverage, prove active-ratio lower bounds,
prove chart-count facts, or invoke the analytic extraction theorem beyond the
explicit chart-level extraction hypothesis supplied as an input.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Case2DisplayedSuppliedChartFamilyBoundary

namespace Case2DisplayedContinuingA0ExponentCoordinateBridge

set_option linter.style.longLine false

/-- Build the supplied chart-final Theorem 2 boundary from a displayed
continuing Case 2 coordinate and chart counts at the displayed Case 2 candidate
ratio.

This is only composition of supplied finite and chart-level boundary data.  It
does not construct the chart certificate or prove the analytic extraction
hypothesis. -/
theorem theorem2SuppliedChartFinalBoundary_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState Lcase n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {Ccase : ℕ → τ → K}
    {cert :
      Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
        Lcase n S J t numerator leastValue pre u residual hS hcont Ccase}
    {Param R : Type*} [CommMonoid R]
    {Cnc : AoyagiNormalCrossingChartCertificate Param R}
    {p : Fin Cnc.numCharts × Fin Cnc.numCoords}
    (B :
      Case2DisplayedContinuingA0ExponentCoordinateBridge cert Cnc.exponentData p)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    {lambda : ℚ} {poleOrder : ℕ}
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hNC : Cnc.ExtractionHypothesis lambda poleOrder)
    (hcenter :
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ Cnc.exponentData.activePairs,
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ≤
        Cnc.exponentData.ratioAt p')
    {c : Fin Cnc.numCharts}
    (hchart :
      Cnc.exponentData.countInChartAtRatio
          (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c =
        data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin Cnc.numCharts,
      Cnc.exponentData.countInChartAtRatio
          (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c' ≤
        data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      Cnc Lthm ell H r cuts m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula :=
    B.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
      data hcenter hleRatio hchart hleChart

end Case2DisplayedContinuingA0ExponentCoordinateBridge

end Aoyagi
end DLN
end DLNFibre
