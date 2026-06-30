import DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasCase2FinalBridge

/-!
# Supplied selected-entry analytic atlas producer

This file names the first non-redundant interface above the finite
selected-entry certificate layer.  The records below are supplied analytic
data: one shared atlas context, source/open coverage, chart and transition
regularity, unit regularity, measure/Jacobian compatibility, produced
branchwise source data, and termination data.

There is deliberately no constructor from finite selected-entry coverage,
finite affine transition regularity, or `SourceProductionObligation`.  The
only theorem is the projection into the existing supplied
`SelectedEntryAnalyticAtlasBoundary` socket.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

open MeasureTheory
open scoped ENNReal

universe uAtlas uBranch

/-- Shared topological atlas context for a supplied selected-entry analytic
producer.

All coverage, regularity, transition, unit, and measure fields below refer to
this same context.  This prevents separate supplied fields from silently using
different chart domains or topologies. -/
structure SelectedEntryAnalyticAtlasContext
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) where
  chartTopology : ∀ c : Fin C.numCharts, TopologicalSpace (C.ChartPoint c)
  sourceDomain : Set Param
  chartDomain : ∀ c : Fin C.numCharts, Set (C.ChartPoint c)
  sourceDomain_isOpen : IsOpen sourceDomain
  chartDomain_isOpen :
    ∀ c : Fin C.numCharts,
      @IsOpen (C.ChartPoint c) (chartTopology c) (chartDomain c)
  sourceDomain_nonempty : sourceDomain.Nonempty

/-- Source-neighborhood coverage data for a supplied selected-entry analytic
atlas producer.

This is stronger than finite selected-entry map coverage: it covers the shared
open source domain by the images of the shared chart domains. -/
structure SelectedEntryAnalyticSourceCoverageData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    (ctx : SelectedEntryAnalyticAtlasContext C) where
  sourceDomain_subset_chart_images :
    ctx.sourceDomain ⊆
      ⋃ c : Fin C.numCharts, C.chartMap c '' ctx.chartDomain c

/-- Chart regularity data on the shared chart domains. -/
structure SelectedEntryAnalyticChartRegularData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    [TopologicalSpace R]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    (ctx : SelectedEntryAnalyticAtlasContext C) where
  chartMap_continuousOn :
    ∀ c : Fin C.numCharts,
      @ContinuousOn (C.ChartPoint c) Param (ctx.chartTopology c) _
        (C.chartMap c) (ctx.chartDomain c)
  coord_continuousOn :
    ∀ (c : Fin C.numCharts) (j : Fin C.numCoords),
      @ContinuousOn (C.ChartPoint c) R (ctx.chartTopology c) _
        (fun x ↦ C.coord c x j) (ctx.chartDomain c)

/-- Transition regularity data on analytic chart overlaps.

The transition maps use the shared chart domains and preserve the represented
source point.  This is intentionally separate from the finite affine
selected-entry transition formulas. -/
structure SelectedEntryAnalyticTransitionRegularData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    (ctx : SelectedEntryAnalyticAtlasContext C) where
  transitionDomain :
    ∀ source _target : Fin C.numCharts, Set (C.ChartPoint source)
  transitionMap :
    ∀ source target : Fin C.numCharts,
      C.ChartPoint source → C.ChartPoint target
  transitionDomain_subset_chartDomain :
    ∀ source target : Fin C.numCharts,
      transitionDomain source target ⊆ ctx.chartDomain source
  transition_continuousOn :
    ∀ source target : Fin C.numCharts,
      @ContinuousOn (C.ChartPoint source) (C.ChartPoint target)
        (ctx.chartTopology source) (ctx.chartTopology target)
        (transitionMap source target) (transitionDomain source target)
  transition_lands :
    ∀ (source target : Fin C.numCharts) (x : C.ChartPoint source),
      x ∈ transitionDomain source target →
        transitionMap source target x ∈ ctx.chartDomain target
  transition_preserves_chartMap :
    ∀ (source target : Fin C.numCharts) (x : C.ChartPoint source),
      x ∈ transitionDomain source target →
        C.chartMap target (transitionMap source target x) =
          C.chartMap source x

/-- Unit regularity data on the shared analytic chart domains.

The finite certificate already carries pointwise `IsUnit` facts everywhere.
This supplied data adds regularity of the unit factors on chart domains. -/
structure SelectedEntryAnalyticUnitRegularData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    [TopologicalSpace R]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    (ctx : SelectedEntryAnalyticAtlasContext C) where
  lossUnit_continuousOn :
    ∀ c : Fin C.numCharts,
      @ContinuousOn (C.ChartPoint c) R (ctx.chartTopology c) _
        (C.lossUnit c) (ctx.chartDomain c)
  jacobianPriorUnit_continuousOn :
    ∀ c : Fin C.numCharts,
      @ContinuousOn (C.ChartPoint c) R (ctx.chartTopology c) _
        (C.jacobianPriorUnit c) (ctx.chartDomain c)
  lossUnit_isUnit_on :
    ∀ (c : Fin C.numCharts) (x : C.ChartPoint c),
      x ∈ ctx.chartDomain c → IsUnit (C.lossUnit c x)
  jacobianPriorUnit_isUnit_on :
    ∀ (c : Fin C.numCharts) (x : C.ChartPoint c),
      x ∈ ctx.chartDomain c → IsUnit (C.jacobianPriorUnit c x)

/-- Measure/Jacobian compatibility data for a supplied analytic atlas.

The field `chart_measure_map_eq_source_restrict` is a genuine chart-domain
pushforward equality.  It prevents the finite pivot-first determinant
calculation from being repackaged as analytic volume-form control. -/
structure SelectedEntryAnalyticJacobianVolumeData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    [MeasurableSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    (ctx : SelectedEntryAnalyticAtlasContext C) where
  chartMeasurableSpace : ∀ c : Fin C.numCharts, MeasurableSpace (C.ChartPoint c)
  chartMeasure : ∀ c : Fin C.numCharts, Measure (C.ChartPoint c)
  sourceMeasure : Measure Param
  density : ∀ c : Fin C.numCharts, C.ChartPoint c → ℝ≥0∞
  chartTarget : ∀ _c : Fin C.numCharts, Set Param
  chartTarget_nonempty : ∀ c : Fin C.numCharts, (chartTarget c).Nonempty
  chartTarget_subset_sourceDomain :
    ∀ c : Fin C.numCharts, chartTarget c ⊆ ctx.sourceDomain
  chartTarget_subset_chart_image :
    ∀ c : Fin C.numCharts, chartTarget c ⊆ C.chartMap c '' ctx.chartDomain c
  source_restrict_neZero :
    ∀ c : Fin C.numCharts, sourceMeasure.restrict (chartTarget c) ≠ 0
  chart_measure_map_eq_source_restrict :
    ∀ c : Fin C.numCharts,
      @Measure.map (C.ChartPoint c) Param (chartMeasurableSpace c) _
        (C.chartMap c)
        (((chartMeasure c).restrict (ctx.chartDomain c)).withDensity
          (density c)) =
        sourceMeasure.restrict (chartTarget c)

/-- Produced source/branch data for one semantic branch. -/
structure SelectedEntryProducedBranchPayload
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    (ctx : SelectedEntryAnalyticAtlasContext C)
    (BranchState : Type uBranch) where
  branchState : BranchState
  producedChart : Fin C.numCharts
  producedPoint : C.ChartPoint producedChart
  producedPoint_mem_chartDomain :
    producedPoint ∈ ctx.chartDomain producedChart
  producedParam : Param
  producedParam_eq_chartMap :
    producedParam = C.chartMap producedChart producedPoint
  producedParam_mem_sourceDomain :
    producedParam ∈ ctx.sourceDomain
  sourceData : Type uBranch
  producedSourceData : sourceData

/-- Produced source/branch data for a supplied selected-entry analytic atlas.

The three branch predicates are separate, because the continuing,
actual-width stopped, and row-exhausted stopped branches carry different
source data.  The payloads are tied to the same branch-state type used by the
termination relation. -/
structure SelectedEntryAtlasProducedBranchData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    (ctx : SelectedEntryAnalyticAtlasContext C)
    (BranchState : Type uBranch) where
  continuingGuard : BranchState → Prop
  actualWidthStoppedGuard : BranchState → Prop
  rowExhaustedStoppedGuard : BranchState → Prop
  continuingPayload :
    ∀ s : BranchState, continuingGuard s →
      SelectedEntryProducedBranchPayload ctx BranchState
  actualWidthStoppedPayload :
    ∀ s : BranchState, actualWidthStoppedGuard s →
      SelectedEntryProducedBranchPayload ctx BranchState
  rowExhaustedStoppedPayload :
    ∀ s : BranchState, rowExhaustedStoppedGuard s →
      SelectedEntryProducedBranchPayload ctx BranchState
  continuing_payload_state :
    ∀ (s : BranchState) (h : continuingGuard s),
      (continuingPayload s h).branchState = s
  actualWidthStopped_payload_state :
    ∀ (s : BranchState) (h : actualWidthStoppedGuard s),
      (actualWidthStoppedPayload s h).branchState = s
  rowExhaustedStopped_payload_state :
    ∀ (s : BranchState) (h : rowExhaustedStoppedGuard s),
      (rowExhaustedStoppedPayload s h).branchState = s

/-- Termination data for the supplied analytic atlas recursion.

This is a genuine well-founded relation on branch states, not a chosen branch
witness.  It is separate from finite branch-domain bookkeeping. -/
structure SelectedEntryBranchTerminationData
    {Param R : Type*} [CommMonoid R]
    (_C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R)
    (BranchState : Type uBranch) where
  step : BranchState → BranchState → Prop
  step_wellFounded : WellFounded step
  initial : BranchState

/-- Branch-progress data connecting supplied branch guards to a supplied
termination relation.

This does not construct source-production payloads or choose a termination
relation.  It names the active branch region, records that the supplied
continuing/stopped guards cover that region, and gives a decreasing child only
for continuing branches.  Stopped branches intentionally have no child here:
they should be handled by terminal payloads, not by fake decreasing steps. -/
structure SelectedEntryAtlasBranchProgressData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    {ctx : SelectedEntryAnalyticAtlasContext C}
    {BranchState : Type uBranch}
    (sourceProduction :
      SelectedEntryAtlasProducedBranchData ctx BranchState)
    (termination :
      SelectedEntryBranchTerminationData C BranchState) where
  activeGuard : BranchState → Prop
  guards_complete :
    ∀ s : BranchState, activeGuard s →
      sourceProduction.continuingGuard s ∨
        sourceProduction.actualWidthStoppedGuard s ∨
          sourceProduction.rowExhaustedStoppedGuard s
  continuingChild :
    ∀ s : BranchState, sourceProduction.continuingGuard s → BranchState
  continuing_child_step :
    ∀ (s : BranchState) (h : sourceProduction.continuingGuard s),
      termination.step (continuingChild s h) s

/- The predicate wrappers below are deliberately forgetful: each exposes one
field shape to the existing boundary socket.  Shared-context coherence lives in
`SelectedEntrySuppliedAnalyticAtlasProducer`; arbitrary boundaries assembled
from these predicates alone need not come from one shared context. -/

/-- Forgetful predicate wrapper for supplied source-neighborhood coverage data. -/
def SelectedEntryAnalyticSourceCoverage
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) : Prop :=
  ∃ ctx : SelectedEntryAnalyticAtlasContext C,
    Nonempty (SelectedEntryAnalyticSourceCoverageData ctx)

/-- Forgetful predicate wrapper for supplied chart regularity data. -/
def SelectedEntryAnalyticChartRegular
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    [TopologicalSpace R]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) : Prop :=
  ∃ ctx : SelectedEntryAnalyticAtlasContext C,
    Nonempty (SelectedEntryAnalyticChartRegularData ctx)

/-- Forgetful predicate wrapper for supplied transition regularity data. -/
def SelectedEntryAnalyticTransitionRegular
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) : Prop :=
  ∃ ctx : SelectedEntryAnalyticAtlasContext C,
    Nonempty (SelectedEntryAnalyticTransitionRegularData ctx)

/-- Forgetful predicate wrapper for supplied unit regularity data. -/
def SelectedEntryAnalyticUnitRegular
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    [TopologicalSpace R]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) : Prop :=
  ∃ ctx : SelectedEntryAnalyticAtlasContext C,
    Nonempty (SelectedEntryAnalyticUnitRegularData ctx)

/-- Forgetful predicate wrapper for supplied analytic Jacobian/volume-form compatibility. -/
def SelectedEntryAnalyticJacobianVolumeCompatible
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    [MeasurableSpace Param]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) : Prop :=
  ∃ ctx : SelectedEntryAnalyticAtlasContext C,
    Nonempty (SelectedEntryAnalyticJacobianVolumeData ctx)

/-- Forgetful predicate wrapper for supplied produced branch/source data. -/
def SelectedEntryAtlasProducedSource
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) : Prop :=
  ∃ ctx : SelectedEntryAnalyticAtlasContext C,
    ∃ BranchState : Type uBranch,
      Nonempty (SelectedEntryAtlasProducedBranchData ctx BranchState)

/-- Forgetful predicate wrapper for supplied branch termination data. -/
def SelectedEntryBranchTermination
    {Param R : Type*} [CommMonoid R]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R) : Prop :=
  ∃ BranchState : Type uBranch,
    Nonempty (SelectedEntryBranchTerminationData C BranchState)

/-- Supplied selected-entry analytic atlas producer.

This is the non-redundant interface above the finite selected-entry layer.  It
has one shared atlas context, and every analytic field refers to it.  No field
is filled by finite selected-entry coverage, finite affine transition
regularity, or formula-level `SourceProductionObligation` constructors in this
file. -/
structure SelectedEntrySuppliedAnalyticAtlasProducer
    (Param R : Type*) [CommMonoid R] [TopologicalSpace Param]
    [TopologicalSpace R] [MeasurableSpace Param] where
  chartCertificate : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R
  BranchState : Type uBranch
  atlasContext :
    SelectedEntryAnalyticAtlasContext chartCertificate
  source_coverage :
    SelectedEntryAnalyticSourceCoverageData atlasContext
  chart_regular :
    SelectedEntryAnalyticChartRegularData atlasContext
  transition_regular :
    SelectedEntryAnalyticTransitionRegularData atlasContext
  unit_regular :
    SelectedEntryAnalyticUnitRegularData atlasContext
  analytic_jacobian_compatible :
    SelectedEntryAnalyticJacobianVolumeData atlasContext
  source_production :
    SelectedEntryAtlasProducedBranchData atlasContext BranchState
  branch_termination :
    SelectedEntryBranchTerminationData chartCertificate BranchState

namespace SelectedEntrySuppliedAnalyticAtlasProducer

variable {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
variable [TopologicalSpace R] [MeasurableSpace Param]

/-- Project a supplied analytic atlas producer into the existing selected-entry
analytic atlas boundary socket.

This projection only wraps the producer's supplied data in the forgetful
predicate interface expected by downstream final bridges.  Shared-context
coherence is carried by the producer before projection; the old boundary socket
does not enforce that coherence for arbitrary inhabitants.  This projection
does not prove extraction, finite exponent formulas, source-rank coverage,
normal crossings, pole order, or RLCT. -/
def toBoundary
    (P : SelectedEntrySuppliedAnalyticAtlasProducer.{uAtlas, uBranch}
      Param R) :
    SelectedEntryAnalyticAtlasBoundary Param R
      SelectedEntryAnalyticSourceCoverage
      SelectedEntryAnalyticChartRegular
      SelectedEntryAnalyticTransitionRegular
      SelectedEntryAnalyticUnitRegular
      SelectedEntryAnalyticJacobianVolumeCompatible
      SelectedEntryAtlasProducedSource
      SelectedEntryBranchTermination where
  chartCertificate := P.chartCertificate
  coverage := ⟨P.atlasContext, ⟨P.source_coverage⟩⟩
  chart_regular := ⟨P.atlasContext, ⟨P.chart_regular⟩⟩
  transition_regular := ⟨P.atlasContext, ⟨P.transition_regular⟩⟩
  unit_regular := ⟨P.atlasContext, ⟨P.unit_regular⟩⟩
  analytic_jacobian_compatible :=
    ⟨P.atlasContext, ⟨P.analytic_jacobian_compatible⟩⟩
  source_production := ⟨P.atlasContext, P.BranchState, ⟨P.source_production⟩⟩
  branch_termination := ⟨P.BranchState, ⟨P.branch_termination⟩⟩

@[simp] theorem toBoundary_chartCertificate
    (P : SelectedEntrySuppliedAnalyticAtlasProducer.{uAtlas, uBranch}
      Param R) :
    P.toBoundary.chartCertificate = P.chartCertificate :=
  rfl

@[simp] theorem toBoundary_exponentData
    (P : SelectedEntrySuppliedAnalyticAtlasProducer.{uAtlas, uBranch}
      Param R) :
    P.toBoundary.exponentData = P.chartCertificate.exponentData :=
  rfl

end SelectedEntrySuppliedAnalyticAtlasProducer

end Aoyagi
end DLN
end DLNFibre
