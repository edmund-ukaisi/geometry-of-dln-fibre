import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducedSourceData
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotSourceCoverageData

/-!
# Produced payloads for all-pivot selected-entry source data

This file lifts the finite Case 2 all-pivot source-data layer to the first
analytic producer payload constructor.  The constructor here is deliberately
fixed-center: it uses the current residual-block center of the supplied
branch state and only covers the continuing displayed Case 2 branch.

It does not instantiate `SelectedEntryAtlasProducedBranchData`, does not cover
the stopped branches, and does not solve recurrence-wide center alignment.
The payload record ties `producedParam` to the chart map at `producedPoint`;
it does not itself state a compatibility invariant between `producedParam`
and the packaged finite `producedSourceData`.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Continuing all-pivot produced branch payload for the current Case 2
residual-block center.

This is one branch payload constructor.  It is not the full all-pivot
source-production field: the stopped branches and recurrence-wide
center-alignment problem remain separate. -/
def case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput
    {tau : Type} {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cfollowing : ℕ → tau → ℝ)
    (hguard : case2AllPivotContinuingGuard s)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    SelectedEntryProducedBranchPayload
      (selectedEntryAllPivotAnalyticAtlasContext
        (case2ResidualBlockPivotEntries_nonempty_of_cont
          n s.stage_pos hguard.1)
        chartEquiv)
      (AoyagiRecurrenceBranchState L n ℝ) := by
  let hactive : s.J + 1 ≤ prefixMinNat n (s.S + 1) := hguard.1
  let hcenter :
      (case2ResidualBlockPivotEntries n s.S s.J).Nonempty :=
    case2ResidualBlockPivotEntries_nonempty_of_cont n s.stage_pos hactive
  let producedChart :=
    chartEquiv.symm
      ⟨(s.J + 1, s.J + 1),
        case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
          n s.stage_pos hactive⟩
  let producedPoint :=
    selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint
      hcenter chartEquiv producedChart
      input.u input.residual
  refine
    { branchState := s
      producedChart := producedChart
      producedPoint := producedPoint
      producedPoint_mem_chartDomain := by
        trivial
      producedParam := _
      producedParam_eq_chartMap := rfl
      producedParam_mem_sourceDomain := by
        trivial
      sourceData :=
        Case2AllPivotContinuingProducedSourceData input Cfollowing
      producedSourceData :=
        Case2AllPivotContinuingProducedSourceData.of_sourceInput
          (input := input) (C := Cfollowing) hguard }

@[simp]
theorem case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput_branchState
    {tau : Type} {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cfollowing : ℕ → tau → ℝ)
    (hguard : case2AllPivotContinuingGuard s)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    (case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput
      input Cfollowing hguard chartEquiv).branchState = s :=
  rfl

end Aoyagi
end DLN
end DLNFibre
