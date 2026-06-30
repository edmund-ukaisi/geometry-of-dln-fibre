import DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasProducer
import DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge

/-!
# One-chart selected-entry Jacobian/volume data

This file packages the finite selected-entry chart-point volume-form
pushforward as one `SelectedEntryAnalyticJacobianVolumeData` field.  The
context uses the single selected-entry chart, `Set.univ` as source and chart
domain, and the signed-box chart image as target.

It does not construct source coverage, transition regularity, source
production, branch termination, a full analytic atlas producer, normal-crossing
extraction, pole order, or an RLCT.
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

/-- The one-chart context used only for the selected-entry Jacobian/volume
field.  Both source and chart domains are `Set.univ`. -/
def selectedEntryOneChartAnalyticAtlasContext
    {center : Finset ι} (pivot : center) :
    SelectedEntryAnalyticAtlasContext
      (selectedEntryCenterSqFormalJacobianChartCertificate (K := ℝ) pivot) where
  chartTopology := fun _ => by
    change TopologicalSpace (FormalChartPoint pivot)
    infer_instance
  sourceDomain := Set.univ
  chartDomain := fun _ => Set.univ
  sourceDomain_isOpen := isOpen_univ
  chartDomain_isOpen := by
    intro _c
    change @IsOpen (FormalChartPoint pivot) inferInstance Set.univ
    exact isOpen_univ
  sourceDomain_nonempty := Set.univ_nonempty

/-- One-chart Jacobian/volume compatibility for the selected-entry
chart-point product measure over a positive signed box.

This fills only the measure/Jacobian compatibility structure for the single
selected-entry chart.  It is not a full analytic atlas producer and proves no
source coverage, transition regularity, source production, normal-crossing
extraction, pole order, or RLCT. -/
def selectedEntryOneChartAnalyticJacobianVolumeData
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    SelectedEntryAnalyticJacobianVolumeData
      (selectedEntryOneChartAnalyticAtlasContext pivot) where
  chartMeasurableSpace := fun _c => by
    change MeasurableSpace (FormalChartPoint pivot)
    infer_instance
  chartMeasure := fun _c => by
    change Measure (FormalChartPoint pivot)
    exact chartPointProductMeasure pivot R
  sourceMeasure := volume
  density := fun _c => by
    change FormalChartPoint pivot → ℝ≥0∞
    exact fun x : FormalChartPoint pivot =>
      ENNReal.ofReal (chartPointDensity pivot x)
  chartTarget := fun _c => chartMap pivot '' signedBoxSet R
  chartTarget_nonempty := by
    intro _c
    rcases chartMapTargetInnerBox_nonempty pivot hR with ⟨x, hx⟩
    exact ⟨x, chartMapTargetInnerBox_subset_chartMap_image_signedBoxSet pivot hR hx⟩
  chartTarget_subset_sourceDomain := by
    intro _c x _hx
    trivial
  chartTarget_subset_chart_image := by
    intro _c
    rintro x ⟨y, hy, rfl⟩
    refine ⟨chartPointAdapter pivot y, ?_, ?_⟩
    · trivial
    · simpa [formalChartMap] using formalChartMap_chartPointAdapter_eq_chartMap pivot y
  source_restrict_neZero := by
    intro _c
    exact volume_restrict_chartMap_image_signedBoxSet_ne_zero pivot hR
  chart_measure_map_eq_source_restrict := by
    intro _c
    simpa [selectedEntryOneChartAnalyticAtlasContext, formalChartMap] using
      map_formalChartMap_chartPointProductMeasure_withDensity_eq_restrict_image pivot R

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
