import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotJacobianVolumeData
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotTransitionRegularData

/-!
# All-pivot selected-entry supplied producer shell

This file assembles the already proved all-pivot selected-entry analytic
coverage, regularity, transition, unit, and Jacobian/volume data into the
`SelectedEntrySuppliedAnalyticAtlasProducer` record.

It keeps the true frontier explicit: branch source production and branch
termination are supplied as inputs.  It does not construct source production,
prove branch termination, extract normal crossings, compute pole order, or
extract an RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace SelectedEntrySignedBox
namespace CenterCoord

universe uBranch

variable {ι : Type*} [DecidableEq ι]

/-- Assemble the all-pivot selected-entry analytic fields into a supplied
producer, with source production and branch termination still explicit. -/
def selectedEntryAllPivotSuppliedAnalyticAtlasProducer
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    {radius : center → ℝ} (hradius : ∀ i, 0 < radius i)
    (BranchState : Type uBranch)
    (sourceProduction :
      SelectedEntryAtlasProducedBranchData
        (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
        BranchState)
    (termination :
      SelectedEntryBranchTerminationData
        (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
          (K := ℝ) hcenter chartEquiv)
        BranchState) :
    SelectedEntrySuppliedAnalyticAtlasProducer (center → ℝ) ℝ where
  chartCertificate :=
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate
      (K := ℝ) hcenter chartEquiv
  BranchState := BranchState
  atlasContext := selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv
  source_coverage :=
    selectedEntryAllPivotAnalyticSourceCoverageData hcenter chartEquiv
  chart_regular :=
    selectedEntryAllPivotAnalyticChartRegularData hcenter chartEquiv
  transition_regular :=
    selectedEntryAllPivotAnalyticTransitionRegularData hcenter chartEquiv
  unit_regular :=
    selectedEntryAllPivotAnalyticUnitRegularData hcenter chartEquiv
  analytic_jacobian_compatible :=
    selectedEntryAllPivotAnalyticJacobianVolumeData hcenter chartEquiv hradius
  source_production := sourceProduction
  branch_termination := termination

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
