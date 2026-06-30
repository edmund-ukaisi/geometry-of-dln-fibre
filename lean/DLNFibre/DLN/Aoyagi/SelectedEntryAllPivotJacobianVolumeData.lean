import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotSourceCoverageData
import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartJacobianVolumeData

/-!
# All-pivot selected-entry Jacobian/volume data

This file lifts the one-pivot selected-entry chart-point volume-form pushforward
chart-by-chart to the shared all-pivot selected-entry atlas context.  It supplies
only `SelectedEntryAnalyticJacobianVolumeData` for the finite all-pivot chart
family.

It does not prove transition regularity, source production, branch termination,
source-prior transport, determinant-chart Haar transport, a full analytic atlas
producer, normal-crossing extraction, pole order, or an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace SelectedEntrySignedBox
namespace CenterCoord

variable {ι : Type*} [DecidableEq ι]

/-- All-pivot Jacobian/volume compatibility for the selected-entry chart-point
product measures over a positive signed box.

For each chart index `c`, this is exactly the one-pivot selected-entry
pushforward theorem at pivot `chartEquiv c`, packaged over the shared all-pivot
universal-domain context. -/
def selectedEntryAllPivotAnalyticJacobianVolumeData
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    SelectedEntryAnalyticJacobianVolumeData
      (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv) where
  chartMeasurableSpace := by
    intro c
    change MeasurableSpace (FormalChartPoint (chartEquiv c))
    infer_instance
  chartMeasure := by
    intro c
    change Measure (FormalChartPoint (chartEquiv c))
    exact chartPointProductMeasure (chartEquiv c) R
  sourceMeasure := volume
  density := by
    intro c
    change FormalChartPoint (chartEquiv c) → ℝ≥0∞
    exact fun x : FormalChartPoint (chartEquiv c) =>
      ENNReal.ofReal (chartPointDensity (chartEquiv c) x)
  chartTarget := fun c => chartMap (chartEquiv c) '' signedBoxSet R
  chartTarget_nonempty := by
    intro c
    rcases chartMapTargetInnerBox_nonempty (chartEquiv c) hR with ⟨x, hx⟩
    exact
      ⟨x, chartMapTargetInnerBox_subset_chartMap_image_signedBoxSet
        (chartEquiv c) hR hx⟩
  chartTarget_subset_sourceDomain := by
    intro c x _hx
    trivial
  chartTarget_subset_chart_image := by
    intro c
    rintro x ⟨y, hy, rfl⟩
    refine ⟨chartPointAdapter (chartEquiv c) y, ?_, ?_⟩
    · trivial
    · simpa [formalChartMap] using
        formalChartMap_chartPointAdapter_eq_chartMap (chartEquiv c) y
  source_restrict_neZero := by
    intro c
    exact volume_restrict_chartMap_image_signedBoxSet_ne_zero (chartEquiv c) hR
  chart_measure_map_eq_source_restrict := by
    intro c
    simpa [selectedEntryAllPivotAnalyticAtlasContext, formalChartMap] using
      map_formalChartMap_chartPointProductMeasure_withDensity_eq_restrict_image
        (chartEquiv c) R

/-- Forgetful predicate wrapper for all-pivot selected-entry Jacobian/volume
compatibility. -/
theorem selectedEntryAllPivotAnalyticJacobianVolumeCompatible
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    SelectedEntryAnalyticJacobianVolumeCompatible
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := ℝ) hcenter chartEquiv) := by
  exact ⟨selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv,
    ⟨selectedEntryAllPivotAnalyticJacobianVolumeData hcenter chartEquiv hR⟩⟩

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
