import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartRegularData

/-!
# One-chart selected-entry analytic predicate data

This file wraps the one-chart selected-entry analytic data records into the
forgetful predicate interface used by `SelectedEntryAnalyticAtlasProducer`.

It does not prove source coverage, construct a supplied analytic atlas
producer, construct source production or branch termination data, perform
normal-crossing extraction, compute pole order, or compute an RLCT.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace SelectedEntrySignedBox
namespace CenterCoord

variable {ι : Type*} [DecidableEq ι]

/-- The one-chart selected-entry context supplies the chart-regularity
predicate for the finite selected-entry normal-crossing certificate. -/
theorem selectedEntryOneChartAnalyticChartRegular
    {center : Finset ι} (pivot : center) :
    SelectedEntryAnalyticChartRegular
      (selectedEntryCenterSqFormalJacobianChartCertificate (K := ℝ) pivot) := by
  exact ⟨selectedEntryOneChartAnalyticAtlasContext pivot,
    ⟨selectedEntryOneChartAnalyticChartRegularData pivot⟩⟩

/-- The one-chart selected-entry context supplies the identity-transition
predicate for the finite selected-entry normal-crossing certificate. -/
theorem selectedEntryOneChartAnalyticTransitionRegular
    {center : Finset ι} (pivot : center) :
    SelectedEntryAnalyticTransitionRegular
      (selectedEntryCenterSqFormalJacobianChartCertificate (K := ℝ) pivot) := by
  exact ⟨selectedEntryOneChartAnalyticAtlasContext pivot,
    ⟨selectedEntryOneChartAnalyticTransitionRegularData pivot⟩⟩

/-- The one-chart selected-entry context supplies the unit-regularity predicate
for the finite selected-entry normal-crossing certificate. -/
theorem selectedEntryOneChartAnalyticUnitRegular
    {center : Finset ι} (pivot : center) :
    SelectedEntryAnalyticUnitRegular
      (selectedEntryCenterSqFormalJacobianChartCertificate (K := ℝ) pivot) := by
  exact ⟨selectedEntryOneChartAnalyticAtlasContext pivot,
    ⟨selectedEntryOneChartAnalyticUnitRegularData pivot⟩⟩

/-- The one-chart selected-entry context supplies the analytic
Jacobian/volume-compatibility predicate for positive signed-box radii. -/
theorem selectedEntryOneChartAnalyticJacobianVolumeCompatible
    {center : Finset ι} (pivot : center) {R : center → ℝ}
    (hR : ∀ i, 0 < R i) :
    SelectedEntryAnalyticJacobianVolumeCompatible
      (selectedEntryCenterSqFormalJacobianChartCertificate (K := ℝ) pivot) := by
  exact ⟨selectedEntryOneChartAnalyticAtlasContext pivot,
    ⟨selectedEntryOneChartAnalyticJacobianVolumeData pivot hR⟩⟩

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
