import DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly

/-!
# Selected-entry analytic atlas boundary to final Theorem 2 socket

This file is a narrow adapter from the supplied selected-entry analytic-atlas
boundary to the existing chart-final Theorem 2 boundary.  It projects the
carried `AoyagiNormalCrossingChartCertificate` and fills the already available
final-socket structure from explicitly supplied final-boundary data.

It does not construct the analytic atlas, prove chart coverage, prove
transition regularity, prove source production, prove finite Theorem 2
exponent formulas, or invoke the normal-crossing extraction theorem beyond the
explicit chart-level extraction hypothesis supplied as an input.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

universe uAtlas

namespace SelectedEntryAnalyticAtlasBoundary

variable {Param R : Type*} [CommMonoid R]
variable {Coverage ChartRegular TransitionRegular UnitRegular
  AnalyticJacobianCompatible SourceProduction BranchTermination :
    AoyagiNormalCrossingChartCertificate.{uAtlas} Param R → Prop}

set_option linter.style.longLine false

/-- Project a supplied selected-entry analytic-atlas boundary to the
chart-final Theorem 2 boundary from the three explicit final-socket inputs:
selected-width provenance, the chart-level extraction hypothesis, and the
finite Theorem 2 exponent formula.

This is only a final-socket adapter.  None of these three inputs is inferred
from the analytic-atlas boundary fields. -/
theorem theorem2SuppliedChartFinalBoundary_of_selectedWidths_eq_reduced_of_extractionHypothesis_of_finiteExponentFormula
    (B : SelectedEntryAnalyticAtlasBoundary Param R Coverage ChartRegular
      TransitionRegular UnitRegular AnalyticJacobianCompatible
      SourceProduction BranchTermination)
    {L ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    {data : AoyagiDefinition3CeilData ell m}
    {lambda : ℚ} {poleOrder : ℕ}
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hNC : (B.chartCertificate).ExtractionHypothesis lambda poleOrder)
    (hFormula :
      AoyagiTheorem2FiniteExponentFormulaHypothesis
        B.exponentData L ell H r m data) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      B.chartCertificate L ell H r cuts m data lambda poleOrder where
  selectedWidths_eq_reduced := hselected
  extractionHypothesis := hNC
  finiteExponentFormula := by
    simpa [SelectedEntryAnalyticAtlasBoundary.exponentData] using hFormula

end SelectedEntryAnalyticAtlasBoundary

end Aoyagi
end DLN
end DLNFibre
