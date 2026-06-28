import DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasFinalBridge
import DLNFibre.DLN.Aoyagi.Case2Theorem2ChartFinalBridge

/-!
# Selected-entry analytic atlas boundary to Case 2 chart-final socket

This file gives a non-vacuous source-production predicate for the supplied
selected-entry analytic-atlas boundary.  The predicate carries a displayed
continuing Case 2 source certificate together with an A0 exponent-coordinate
bridge for the same supplied chart certificate.  The final theorem only
unwraps that payload and calls the existing Case 2/A0 chart-final bridge.

It does not construct analytic charts, prove coverage, prove regularity or
transition regularity, prove analytic Jacobian/volume-form compatibility,
produce successor or suffix data, prove normal crossings, or extract an RLCT.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

universe uAtlas

open Case2DisplayedSuppliedChartFamilyBoundary

set_option linter.style.longLine false

/-- Data-bearing source-production payload for the selected-entry analytic
atlas boundary in the displayed continuing Case 2 lane.

The payload is intentionally stronger than `True` or formula-level successor
bookkeeping: it contains a displayed Case 2 source-chart certificate and a
coordinate bridge into the exponent data of the same supplied A0 chart
certificate.  It is still supplied data; this structure does not construct the
analytic atlas or prove that the source calculation is produced by it. -/
structure SelectedEntryCase2DisplayedA0SourceProductionData
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState Lcase n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {Ccase : ℕ → τ → K}
    {Param R : Type*} [CommMonoid R]
    (Cnc : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) where
  cert :
    Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate
      Lcase n S J t numerator leastValue pre u residual hS hcont Ccase
  activeCoord : Fin Cnc.numCharts × Fin Cnc.numCoords
  a0Coord :
    Case2DisplayedContinuingA0ExponentCoordinateBridge
      cert Cnc.exponentData activeCoord

/-- Propositional source-production predicate for a supplied selected-entry
analytic-atlas boundary in the displayed continuing Case 2 lane.

Using `Nonempty` keeps the atlas boundary field propositional while requiring
real source-production payload data. -/
def SelectedEntryCase2DisplayedA0SourceProduction
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState Lcase n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {Ccase : ℕ → τ → K}
    {Param R : Type*} [CommMonoid R]
    (Cnc : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) : Prop :=
  Nonempty
    (SelectedEntryCase2DisplayedA0SourceProductionData
      (τ := τ) (K := K) (Lcase := Lcase) (n := n) (S := S) (J := J)
      (t := t) (numerator := numerator) (leastValue := leastValue)
      (pre := pre) (u := u) (residual := residual) (hS := hS)
      (hcont := hcont) (Ccase := Ccase) Cnc)

namespace SelectedEntryCase2DisplayedA0SourceProduction

/-- Construct displayed Case 2 source-production payload for the concrete
all-pivot finite selected-entry chart certificate.

This fills only the `SelectedEntryCase2DisplayedA0SourceProduction` predicate
for `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`.  It does
not construct an analytic atlas, prove coverage or regularity, prove analytic
Jacobian compatibility, or supply global active-ratio/chart-count hypotheses. -/
theorem of_case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (pre : IntroducedLabelRecurrenceState Lcase n S J K)
    (u : K) (residual : ℕ × ℕ → K)
    (hS : 1 ≤ S) (hSL : S ≤ Lcase)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (exponentPre : IntroducedLabelExponentCertificates Lcase n S J t numerator leastValue)
    (levelInv : IntroducedLabelLevelInvariants Lcase n S J pre.level leastValue)
    (leastValueGap : case2IntroducedLabelLeastValueGap Lcase n S J leastValue)
    (Ccase : ℕ → τ → K)
    (c : Fin (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
      (K := K) n hS hcont).exponentData.numCharts) :
    SelectedEntryCase2DisplayedA0SourceProduction
      (τ := τ) (K := K) (Lcase := Lcase) (n := n) (S := S) (J := J)
      (t := t) (numerator := numerator) (leastValue := leastValue)
      (pre := pre) (u := u) (residual := residual) (hS := hS)
      (hcont := hcont) (Ccase := Ccase)
      (case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
        (K := K) n hS hcont) := by
  let cert :=
    sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily
      pre u residual hS hSL hcont hnext exponentPre levelInv leastValueGap
      Ccase
  refine ⟨?_⟩
  refine
    { cert := cert
      activeCoord := (c, (0 : Fin 1))
      a0Coord := ?_ }
  exact
    { toExponentCoordinateBridge :=
        case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.localExponentCoordinateBridge_anyChart
          cert c }

end SelectedEntryCase2DisplayedA0SourceProduction

namespace SelectedEntryAnalyticAtlasBoundary

variable {Param R : Type*} [CommMonoid R]
variable {Coverage ChartRegular TransitionRegular UnitRegular
  AnalyticJacobianCompatible BranchTermination :
    AoyagiNormalCrossingChartCertificate.{uAtlas} Param R → Prop}

/-- Consume displayed Case 2 source-production payload carried by a supplied
selected-entry analytic-atlas boundary and feed it into the existing A0
chart-final Theorem 2 socket.

All global final-socket hypotheses remain explicit: selected-width
provenance, chart-level extraction, identification of the displayed local
ratio with the Definition 3 lambda formula, the active-ratio lower bound, and
the chart-count equality/upper bound. -/
theorem theorem2SuppliedChartFinalBoundary_of_case2DisplayedA0SourceProduction
    {τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Lcase : ℕ} {n : ℕ → ℕ} {S J : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {pre : IntroducedLabelRecurrenceState Lcase n S J K}
    {u : K} {residual : ℕ × ℕ → K}
    {hS : 1 ≤ S} {hcont : J + 1 ≤ prefixMinNat n (S + 1)}
    {Ccase : ℕ → τ → K}
    (B : SelectedEntryAnalyticAtlasBoundary Param R Coverage ChartRegular
      TransitionRegular UnitRegular AnalyticJacobianCompatible
      (SelectedEntryCase2DisplayedA0SourceProduction
        (τ := τ) (K := K) (Lcase := Lcase) (n := n) (S := S) (J := J)
        (t := t) (numerator := numerator) (leastValue := leastValue)
        (pre := pre) (u := u) (residual := residual) (hS := hS)
        (hcont := hcont) (Ccase := Ccase))
      BranchTermination)
    {Lthm ell : ℕ} {H : ℕ → ℕ} {r : ℕ}
    {cuts : AoyagiSelectedCutpoints ell} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    {lambda : ℚ} {poleOrder : ℕ}
    (hselected : m = aoyagiSelectedReducedWidths H r cuts)
    (hNC : B.chartCertificate.ExtractionHypothesis lambda poleOrder)
    (hcenter :
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 =
        aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data)
    (hleRatio : ∀ p' ∈ B.chartCertificate.exponentData.activePairs,
      ((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2 ≤
        B.chartCertificate.exponentData.ratioAt p')
    {c : Fin B.chartCertificate.numCharts}
    (hchart :
      B.chartCertificate.exponentData.countInChartAtRatio
          (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c =
        data.theorem2OrderFormula)
    (hleChart : ∀ c' : Fin B.chartCertificate.numCharts,
      B.chartCertificate.exponentData.countInChartAtRatio
          (((case2ResidualBlockPivotEntries n S J).card : ℚ) / 2) c' ≤
        data.theorem2OrderFormula) :
    AoyagiTheorem2SuppliedChartFinalBoundary
      B.chartCertificate Lthm ell H r cuts m data lambda poleOrder := by
  rcases
    (B.source_production :
      Nonempty
        (SelectedEntryCase2DisplayedA0SourceProductionData
          (τ := τ) (K := K) (Lcase := Lcase) (n := n) (S := S) (J := J)
          (t := t) (numerator := numerator) (leastValue := leastValue)
          (pre := pre) (u := u) (residual := residual) (hS := hS)
          (hcont := hcont) (Ccase := Ccase) B.chartCertificate)) with
    ⟨payload⟩
  exact
    payload.a0Coord.theorem2SuppliedChartFinalBoundary_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le
      data hselected hNC hcenter hleRatio hchart hleChart

end SelectedEntryAnalyticAtlasBoundary

end Aoyagi
end DLN
end DLNFibre
