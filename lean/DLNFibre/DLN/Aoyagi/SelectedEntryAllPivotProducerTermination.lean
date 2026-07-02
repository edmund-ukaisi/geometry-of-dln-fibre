import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducerShell
import DLNFibre.DLN.Aoyagi.SelectedEntryBranchProgressBridge

/-!
# All-pivot selected-entry producer with recurrence termination

This file removes the separate branch-termination input from the all-pivot
selected-entry producer in the recurrence-aware branch-state case.  It still
keeps source production and the initial recurrence data explicit.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace SelectedEntrySignedBox
namespace CenterCoord

universe uBranch

variable {ι : Type*} [DecidableEq ι]

/-- Assemble the all-pivot selected-entry producer using recurrence-aware
branch termination data. -/
def selectedEntryAllPivotSuppliedAnalyticAtlasProducerWithRecurrenceTermination
    {center : Finset ι} (hcenter : center.Nonempty)
    (chartEquiv : Fin center.card ≃ center)
    {radius : center → ℝ} (hradius : ∀ i, 0 < radius i)
    (L : ℕ) (n : ℕ → ℕ) (α : Type uBranch) (hL : 1 ≤ L)
    (initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 α)
    (sourceProduction :
      SelectedEntryAtlasProducedBranchData
        (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
        (AoyagiRecurrenceBranchState L n α)) :
    SelectedEntrySuppliedAnalyticAtlasProducer (center → ℝ) ℝ :=
  selectedEntryAllPivotSuppliedAnalyticAtlasProducer
    hcenter chartEquiv hradius
    (AoyagiRecurrenceBranchState L n α)
    sourceProduction
    (selectedEntryRecurrenceBranchTerminationData
      (selectedEntryCenterSqFormalJacobianChartFamilyCertificate
        (K := ℝ) hcenter chartEquiv)
      L n α hL initialRecurrence)

end CenterCoord
end SelectedEntrySignedBox

end Aoyagi
end DLN
end DLNFibre
