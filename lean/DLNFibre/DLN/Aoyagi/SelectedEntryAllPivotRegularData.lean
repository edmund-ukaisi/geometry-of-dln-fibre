import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotSourceCoverageData
import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartRegularData

/-!
# All-pivot selected-entry regularity data

This file lifts the one-pivot selected-entry chart and unit regularity facts
chart-by-chart to the shared all-pivot selected-entry atlas context.  It does
not prove transition regularity, Jacobian/volume compatibility, source
production, branch termination, normal-crossing extraction, pole order, or an
RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open SelectedEntrySignedBox.CenterCoord

variable {ι : Type*} [DecidableEq ι]

/-- All-pivot selected-entry chart regularity for the shared universal-domain
all-pivot context.

Each all-pivot chart is definitionally the one-pivot selected-entry chart at
`chartEquiv c`, so this records the already-proved one-pivot continuity facts
without adding transition or coverage claims. -/
def selectedEntryAllPivotAnalyticChartRegularData
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticChartRegularData
      (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv) where
  chartMap_continuousOn := by
    intro c
    change @ContinuousOn (FormalChartPoint (chartEquiv c)) (center → ℝ)
      inferInstance inferInstance (formalChartMap (chartEquiv c)) Set.univ
    exact (continuous_formalChartMap (chartEquiv c)).continuousOn
  coord_continuousOn := by
    intro c j
    fin_cases j
    change @ContinuousOn (FormalChartPoint (chartEquiv c)) ℝ
      inferInstance inferInstance
      (fun x : FormalChartPoint (chartEquiv c) =>
        (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) (chartEquiv c)).coord (0 : Fin 1) x (0 : Fin 1))
      Set.univ
    exact (continuous_chartPointCoord (chartEquiv c)).continuousOn

/-- All-pivot selected-entry unit regularity for the shared universal-domain
all-pivot context.

This supplies continuity and pointwise `IsUnit` facts for the loss and formal
Jacobian/prior units in every selected-entry pivot chart. -/
def selectedEntryAllPivotAnalyticUnitRegularData
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticUnitRegularData
      (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv) where
  lossUnit_continuousOn := by
    intro c
    change @ContinuousOn (FormalChartPoint (chartEquiv c)) ℝ
      inferInstance inferInstance
      (fun x : FormalChartPoint (chartEquiv c) =>
        (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) (chartEquiv c)).lossUnit (0 : Fin 1) x)
      Set.univ
    exact (continuous_chartPointLossUnit (chartEquiv c)).continuousOn
  jacobianPriorUnit_continuousOn := by
    intro c
    change @ContinuousOn (FormalChartPoint (chartEquiv c)) ℝ
      inferInstance inferInstance
      (fun x : FormalChartPoint (chartEquiv c) =>
        (selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) (chartEquiv c)).jacobianPriorUnit (0 : Fin 1) x)
      Set.univ
    exact (continuous_chartPointJacobianPriorUnit (chartEquiv c)).continuousOn
  lossUnit_isUnit_on := by
    intro c x _hx
    change
      IsUnit
        ((selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) (chartEquiv c)).lossUnit (0 : Fin 1) x)
    exact
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := ℝ) (chartEquiv c)).lossUnit_isUnit (0 : Fin 1) x
  jacobianPriorUnit_isUnit_on := by
    intro c x _hx
    change
      IsUnit
        ((selectedEntryCenterSqFormalJacobianChartCertificate
          (K := ℝ) (chartEquiv c)).jacobianPriorUnit (0 : Fin 1) x)
    exact
      (selectedEntryCenterSqFormalJacobianChartCertificate
        (K := ℝ) (chartEquiv c)).jacobianPriorUnit_isUnit (0 : Fin 1) x

/-- Forgetful predicate wrapper for all-pivot selected-entry chart
regularity.

This wraps only `SelectedEntryAnalyticChartRegularData` for the shared
all-pivot context; it is not a full analytic atlas producer. -/
theorem selectedEntryAllPivotAnalyticChartRegular
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticChartRegular
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := ℝ) hcenter chartEquiv) := by
  exact ⟨selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv,
    ⟨selectedEntryAllPivotAnalyticChartRegularData hcenter chartEquiv⟩⟩

/-- Forgetful predicate wrapper for all-pivot selected-entry unit regularity.

This wraps only `SelectedEntryAnalyticUnitRegularData` for the shared
all-pivot context; it is not a full analytic atlas producer. -/
theorem selectedEntryAllPivotAnalyticUnitRegular
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) :
    SelectedEntryAnalyticUnitRegular
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := ℝ) hcenter chartEquiv) := by
  exact ⟨selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv,
    ⟨selectedEntryAllPivotAnalyticUnitRegularData hcenter chartEquiv⟩⟩

end Aoyagi
end DLN
end DLNFibre
