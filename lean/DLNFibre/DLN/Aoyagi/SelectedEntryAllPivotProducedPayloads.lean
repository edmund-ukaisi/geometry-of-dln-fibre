import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducedSourceData
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotSourceCoverageData

/-!
# Produced payloads for all-pivot selected-entry source data

This file lifts the finite Case 2 all-pivot source-data layer to the first
analytic producer payload constructors.  The constructors here are
deliberately fixed-center: they use the current residual-block center of the
supplied branch state and cover the continuing branch plus the stopped
subcases already represented by finite source data.

It does not instantiate `SelectedEntryAtlasProducedBranchData`, does not merge
the stopped subcases into one total row-exhausted payload, and does not solve
recurrence-wide center alignment.
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

/-- Actual-width stopped all-pivot produced branch payload for the current
Case 2 residual-block center. -/
def case2AllPivotActualWidthStoppedProducedBranchPayload_of_currentCenterSourceInput
    {upsilon tau : Type} [Fintype tau]
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cterminal : ℕ → tau → ℝ)
    (Fterminal : Matrix tau upsilon ℝ)
    (hguard : case2AllPivotActualWidthStoppedGuard s)
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
        Case2AllPivotActualWidthStoppedProducedSourceData
          input Cterminal Fterminal
      producedSourceData :=
        Case2AllPivotActualWidthStoppedProducedSourceData.of_sourceInput
          (input := input) (C := Cterminal) (F := Fterminal) hguard }

@[simp]
theorem case2AllPivotActualWidthStoppedProducedBranchPayload_of_currentCenterSourceInput_branchState
    {upsilon tau : Type} [Fintype tau]
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cterminal : ℕ → tau → ℝ)
    (Fterminal : Matrix tau upsilon ℝ)
    (hguard : case2AllPivotActualWidthStoppedGuard s)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    (case2AllPivotActualWidthStoppedProducedBranchPayload_of_currentCenterSourceInput
      input Cterminal Fterminal hguard chartEquiv).branchState = s :=
  rfl

@[simp]
theorem case2AllPivotActualWidthStoppedPayload_sourceData
    {upsilon tau : Type} [Fintype tau]
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cterminal : ℕ → tau → ℝ)
    (Fterminal : Matrix tau upsilon ℝ)
    (hguard : case2AllPivotActualWidthStoppedGuard s)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    (case2AllPivotActualWidthStoppedProducedBranchPayload_of_currentCenterSourceInput
      input Cterminal Fterminal hguard chartEquiv).sourceData =
      Case2AllPivotActualWidthStoppedProducedSourceData
        input Cterminal Fterminal :=
  rfl

/-- Terminal-last row-exhausted all-pivot produced branch payload for the
current Case 2 residual-block center. -/
def case2AllPivotRowExhaustedTerminalLastProducedBranchPayload_of_currentCenterSourceInput
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {kappa : Fin (L + 1) → Type}
    [∀ i, Finite (kappa i)]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Ctail : ∀ p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) ℝ)
    (hguard : case2AllPivotRowExhaustedTerminalLastGuard s)
    (Cterminal :
      ℕ → kappa (sourceLayerIndex L (s.S + 2)
        (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
        (Nat.succ_le_succ (le_of_eq hguard.2))) → ℝ)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    SelectedEntryProducedBranchPayload
      (selectedEntryAllPivotAnalyticAtlasContext
        (case2ResidualBlockPivotEntries_nonempty_of_cont
          n s.stage_pos hguard.1.1)
        chartEquiv)
      (AoyagiRecurrenceBranchState L n ℝ) := by
  let hactive : s.J + 1 ≤ prefixMinNat n (s.S + 1) := hguard.1.1
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
        Case2AllPivotRowExhaustedTerminalLastProducedSourceData
          input kappa hguard.2 Cterminal Ctail
      producedSourceData :=
        Case2AllPivotRowExhaustedTerminalLastProducedSourceData.of_sourceInput
          (input := input) (Ctail := Ctail) hguard Cterminal }

@[simp]
theorem case2AllPivotRowExhaustedTerminalLastProducedBranchPayload_branchState
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {kappa : Fin (L + 1) → Type}
    [∀ i, Finite (kappa i)]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Ctail : ∀ p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) ℝ)
    (hguard : case2AllPivotRowExhaustedTerminalLastGuard s)
    (Cterminal :
      ℕ → kappa (sourceLayerIndex L (s.S + 2)
        (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
        (Nat.succ_le_succ (le_of_eq hguard.2))) → ℝ)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    (case2AllPivotRowExhaustedTerminalLastProducedBranchPayload_of_currentCenterSourceInput
      input Ctail hguard Cterminal chartEquiv).branchState = s :=
  rfl

@[simp]
theorem case2AllPivotRowExhaustedTerminalLastPayload_sourceData
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {kappa : Fin (L + 1) → Type}
    [∀ i, Finite (kappa i)]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Ctail : ∀ p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) ℝ)
    (hguard : case2AllPivotRowExhaustedTerminalLastGuard s)
    (Cterminal :
      ℕ → kappa (sourceLayerIndex L (s.S + 2)
        (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
        (Nat.succ_le_succ (le_of_eq hguard.2))) → ℝ)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    (case2AllPivotRowExhaustedTerminalLastProducedBranchPayload_of_currentCenterSourceInput
      input Ctail hguard Cterminal chartEquiv).sourceData =
      Case2AllPivotRowExhaustedTerminalLastProducedSourceData
        input kappa hguard.2 Cterminal Ctail :=
  rfl

/-- Source-suffix row-exhausted all-pivot produced branch payload for the
current Case 2 residual-block center. -/
def case2AllPivotRowExhaustedSourceSuffixProducedBranchPayload_of_currentCenterSourceInput
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {kappa : Fin (L + 1) → Type}
    [∀ i, Fintype (kappa i)] [∀ i, DecidableEq (kappa i)]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Ctail : ∀ p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) ℝ)
    (hguard : case2AllPivotRowExhaustedSourceSuffixGuard s)
    (Csuffix :
      ℕ → kappa (sourceLayerIndex L (s.S + 2)
        (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
        (Nat.succ_le_succ hguard.2)) → ℝ)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    SelectedEntryProducedBranchPayload
      (selectedEntryAllPivotAnalyticAtlasContext
        (case2ResidualBlockPivotEntries_nonempty_of_cont
          n s.stage_pos hguard.1.1)
        chartEquiv)
      (AoyagiRecurrenceBranchState L n ℝ) := by
  let hactive : s.J + 1 ≤ prefixMinNat n (s.S + 1) := hguard.1.1
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
        Case2AllPivotRowExhaustedSourceSuffixProducedSourceData
          input kappa hguard.2 Csuffix Ctail
      producedSourceData :=
        Case2AllPivotRowExhaustedSourceSuffixProducedSourceData.of_sourceInput
          (input := input) (Ctail := Ctail) hguard Csuffix }

@[simp]
theorem case2AllPivotRowExhaustedSourceSuffixProducedBranchPayload_branchState
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {kappa : Fin (L + 1) → Type}
    [∀ i, Fintype (kappa i)] [∀ i, DecidableEq (kappa i)]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Ctail : ∀ p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) ℝ)
    (hguard : case2AllPivotRowExhaustedSourceSuffixGuard s)
    (Csuffix :
      ℕ → kappa (sourceLayerIndex L (s.S + 2)
        (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
        (Nat.succ_le_succ hguard.2)) → ℝ)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    (case2AllPivotRowExhaustedSourceSuffixProducedBranchPayload_of_currentCenterSourceInput
      input Ctail hguard Csuffix chartEquiv).branchState = s :=
  rfl

@[simp]
theorem case2AllPivotRowExhaustedSourceSuffixPayload_sourceData
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n ℝ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {kappa : Fin (L + 1) → Type}
    [∀ i, Fintype (kappa i)] [∀ i, DecidableEq (kappa i)]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Ctail : ∀ p : Fin L, Matrix (kappa p.castSucc) (kappa p.succ) ℝ)
    (hguard : case2AllPivotRowExhaustedSourceSuffixGuard s)
    (Csuffix :
      ℕ → kappa (sourceLayerIndex L (s.S + 2)
        (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
        (Nat.succ_le_succ hguard.2)) → ℝ)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    (case2AllPivotRowExhaustedSourceSuffixProducedBranchPayload_of_currentCenterSourceInput
      input Ctail hguard Csuffix chartEquiv).sourceData =
      Case2AllPivotRowExhaustedSourceSuffixProducedSourceData
        input kappa hguard.2 Csuffix Ctail :=
  rfl

end Aoyagi
end DLN
end DLNFibre
