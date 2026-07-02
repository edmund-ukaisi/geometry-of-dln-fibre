import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducedPayloads

/-!
# Branch-indexed current-center payloads for all-pivot Case 2

The fixed-center payload constructors in
`SelectedEntryAllPivotProducedPayloads` are deliberately local to the current
Case 2 residual-block center
`case2ResidualBlockPivotEntries n s.S s.J`.

This file records the next support interface honestly: branch-indexed payload
data may vary its selected-entry center with the branch state.  This is not a
`SelectedEntryAtlasProducedBranchData`, because that producer record has one
fixed atlas context and hence one fixed center for all branch states.

It also names the exact fixed-center alignment condition that would be needed
before current-center payloads could be used in a recurrence-wide fixed-center
producer.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The current Case 2 residual-block center attached to one recurrence branch
state. -/
def case2AllPivotCurrentCenter
    {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiRecurrenceBranchState L n ℝ) : Finset (ℕ × ℕ) :=
  case2ResidualBlockPivotEntries n s.S s.J

/-- A fixed all-pivot center is aligned with a branch state when it equals the
state's current Case 2 residual-block center. -/
def case2AllPivotFixedCenterAligned
    {L : ℕ} {n : ℕ → ℕ}
    (center : Finset (ℕ × ℕ))
    (s : AoyagiRecurrenceBranchState L n ℝ) : Prop :=
  center = case2AllPivotCurrentCenter s

/-- The Case 2 current residual-block center changes after a same-stage
`J -> J+1` pivot.

This is the finite center-change obstruction behind the fixed-center alignment
contract.  It does not assert that no fixed-context producer can be supplied by
other means; it only rules out reusing current-center payloads across the
continuing edge without center transport or a dependent branch-indexed atlas. -/
theorem case2ResidualBlockPivotEntries_ne_succ_of_cont
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1)) :
    case2ResidualBlockPivotEntries n S J ≠
      case2ResidualBlockPivotEntries n S (J + 1) := by
  intro hcenter
  have hp :
      (J + 1, J + 1) ∈ case2ResidualBlockPivotEntries n S J :=
    case2_displayedPivot_mem_residualBlockPivotEntries_of_cont
      n hS hcont
  have hpSucc :
      (J + 1, J + 1) ∈ case2ResidualBlockPivotEntries n S (J + 1) := by
    simpa [hcenter] using hp
  have hbounds :=
    (mem_case2ResidualBlockPivotEntries_iff n S (J + 1) (J + 1) (J + 1)).mp
      hpSucc
  omega

/-- Along a continuing same-stage child edge, the branch-indexed current center
changes. -/
theorem case2AllPivotCurrentCenter_ne_sameStageChildWithRecurrence_of_continuing
    {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiRecurrenceBranchState L n ℝ)
    (recurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) ℝ)
    (hguard : case2AllPivotContinuingGuard s) :
    case2AllPivotCurrentCenter s ≠
      case2AllPivotCurrentCenter
        (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence
          s recurrence) := by
  simpa [case2AllPivotCurrentCenter,
    AoyagiRecurrenceBranchState.sameStageChildWithRecurrence] using
    case2ResidualBlockPivotEntries_ne_succ_of_cont n s.stage_pos hguard.1

/-- The same-stage child of a continuing Case 2 branch is itself Case 2
active. -/
theorem case2AllPivot_sameStageChild_active_of_continuing
    {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiRecurrenceBranchState L n ℝ)
    (recurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) ℝ)
    (hguard : case2AllPivotContinuingGuard s) :
    AoyagiRecurrenceBranchState.case2DisplayedActiveGuard
      (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence
        s recurrence) := by
  simpa [case2AllPivotContinuingGuard,
    AoyagiRecurrenceBranchState.case2DisplayedActiveContinuingGuard,
    AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard,
    AoyagiRecurrenceBranchState.case2DisplayedActiveGuard,
    AoyagiRecurrenceBranchState.sameStageChildWithRecurrence,
    AoyagiRecurrenceBranchState.toIntroducedState] using hguard.2

/-- A single fixed center cannot be current-center aligned with both a
continuing state and its same-stage child. -/
theorem not_fixedCenterAligned_parent_and_sameStageChild_of_continuing
    {center : Finset (ℕ × ℕ)}
    {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiRecurrenceBranchState L n ℝ)
    (recurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) ℝ)
    (hguard : case2AllPivotContinuingGuard s) :
    ¬ (case2AllPivotFixedCenterAligned center s ∧
      case2AllPivotFixedCenterAligned center
        (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence
          s recurrence)) := by
  intro haligned
  have hne :=
    case2AllPivotCurrentCenter_ne_sameStageChildWithRecurrence_of_continuing
      s recurrence hguard
  have heq :
      case2AllPivotCurrentCenter s =
        case2AllPivotCurrentCenter
          (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence
            s recurrence) :=
    haligned.1.symm.trans haligned.2
  exact hne heq

/-- Fixed-center compatibility needed to reuse current-center Case 2 payloads
inside one recurrence-wide all-pivot atlas context.

The condition is intentionally strong: for every active recurrence state, the
fixed center must be exactly the current residual-block center for that state.
Without such an alignment field, the fixed-center all-pivot producer is typed
against the wrong chart certificate for some branch states.

This is a contract, not a proof that the condition holds in Aoyagi's
recurrence. -/
structure Case2AllPivotFixedCenterAlignment
    (center : Finset (ℕ × ℕ)) (L : ℕ) (n : ℕ → ℕ) where
  center_eq_of_active :
    ∀ s : AoyagiRecurrenceBranchState L n ℝ,
      AoyagiRecurrenceBranchState.case2DisplayedActiveGuard s →
        case2AllPivotFixedCenterAligned center s

namespace Case2AllPivotFixedCenterAlignment

variable {center : Finset (ℕ × ℕ)} {L : ℕ} {n : ℕ → ℕ}
variable {s : AoyagiRecurrenceBranchState L n ℝ}

/-- Fixed-center alignment specializes to a continuing active guard. -/
theorem center_eq_of_continuing
    (A : Case2AllPivotFixedCenterAlignment center L n)
    (h : case2AllPivotContinuingGuard s) :
    center = case2ResidualBlockPivotEntries n s.S s.J :=
  A.center_eq_of_active s h.1

/-- Fixed-center alignment specializes to an actual-width stopped active
guard. -/
theorem center_eq_of_actualWidthStopped
    (A : Case2AllPivotFixedCenterAlignment center L n)
    (h : case2AllPivotActualWidthStoppedGuard s) :
    center = case2ResidualBlockPivotEntries n s.S s.J :=
  A.center_eq_of_active s h.1

/-- Fixed-center alignment specializes to a terminal-last row-exhausted active
guard. -/
theorem center_eq_of_rowExhaustedTerminalLast
    (A : Case2AllPivotFixedCenterAlignment center L n)
    (h : case2AllPivotRowExhaustedTerminalLastGuard s) :
    center = case2ResidualBlockPivotEntries n s.S s.J :=
  A.center_eq_of_active s h.1.1

/-- Fixed-center alignment specializes to a source-suffix row-exhausted active
guard. -/
theorem center_eq_of_rowExhaustedSourceSuffix
    (A : Case2AllPivotFixedCenterAlignment center L n)
    (h : case2AllPivotRowExhaustedSourceSuffixGuard s) :
    center = case2ResidualBlockPivotEntries n s.S s.J :=
  A.center_eq_of_active s h.1.1

/-- A fixed-center alignment over every active state is incompatible with a
continuing same-stage edge.

This is still only a current-center obstruction.  It does not rule out a
separately supplied fixed-context producer whose payloads are transported by
additional data. -/
theorem not_alignment_of_continuing
    (s : AoyagiRecurrenceBranchState L n ℝ)
    (recurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) ℝ)
    (h : case2AllPivotContinuingGuard s) :
    ¬ Case2AllPivotFixedCenterAlignment center L n := by
  intro A
  exact
    not_fixedCenterAligned_parent_and_sameStageChild_of_continuing
      (center := center) s recurrence h
      ⟨A.center_eq_of_active s h.1,
        A.center_eq_of_active
          (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence
            s recurrence)
          (case2AllPivot_sameStageChild_active_of_continuing
            s recurrence h)⟩

end Case2AllPivotFixedCenterAlignment

/-- A produced payload over the current Case 2 residual-block center of one
recurrence branch state.

The center and chart equivalence are part of the package, so this record can
vary with `s`.  It is therefore branch-indexed source-production support, not
the fixed-context producer field `SelectedEntryAtlasProducedBranchData`. -/
structure Case2AllPivotCurrentCenterProducedPayload
    {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiRecurrenceBranchState L n ℝ)
    (hactive : s.J + 1 ≤ prefixMinNat n (s.S + 1)) where
  chartEquiv :
    Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
      (case2ResidualBlockPivotEntries n s.S s.J : Type)
  payload :
    SelectedEntryProducedBranchPayload
      (selectedEntryAllPivotAnalyticAtlasContext
        (case2ResidualBlockPivotEntries_nonempty_of_cont
          n s.stage_pos hactive)
        chartEquiv)
      (AoyagiRecurrenceBranchState L n ℝ)
  payload_state : payload.branchState = s

namespace Case2AllPivotCurrentCenterProducedPayload

variable {υ τ : Type} {L : ℕ} {n : ℕ → ℕ}
variable {s : AoyagiRecurrenceBranchState L n ℝ}
variable {t : ℕ → ℕ → ℕ → ℤ}
variable {numerator leastValue : ℕ → ℕ → ℤ}

/-- Package the continuing fixed-current-center payload as branch-indexed
current-center data. -/
def of_continuing
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cfollowing : ℕ → τ → ℝ)
    (hguard : case2AllPivotContinuingGuard s)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    Case2AllPivotCurrentCenterProducedPayload s hguard.1 where
  chartEquiv := chartEquiv
  payload :=
    case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput
      input Cfollowing hguard chartEquiv
  payload_state := rfl

@[simp]
theorem of_continuing_payload_sourceData
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cfollowing : ℕ → τ → ℝ)
    (hguard : case2AllPivotContinuingGuard s)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    ((of_continuing input Cfollowing hguard chartEquiv).payload).sourceData =
      Case2AllPivotContinuingProducedSourceData input Cfollowing :=
  rfl

/-- The branch-indexed continuing wrapper exposes the same child-progress
projection as the fixed-current-center continuing payload it wraps. -/
theorem of_continuing_payload_child_progress
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cfollowing : ℕ → τ → ℝ)
    (hguard : case2AllPivotContinuingGuard s)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    let produced :=
      (of_continuing input Cfollowing hguard chartEquiv).payload.producedSourceData
    AoyagiRecurrenceBranchState.progressStep L n ℝ
      (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence s produced.childRecurrence)
      s := by
  simpa [of_continuing] using
    case2AllPivotContinuingProducedBranchPayload_child_progress
      input Cfollowing hguard chartEquiv

/-- Package the actual-width stopped fixed-current-center payload as
branch-indexed current-center data. -/
def of_actualWidthStopped
    [Fintype τ]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Cterminal : ℕ → τ → ℝ)
    (Fterminal : Matrix τ υ ℝ)
    (hguard : case2AllPivotActualWidthStoppedGuard s)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    Case2AllPivotCurrentCenterProducedPayload s hguard.1 where
  chartEquiv := chartEquiv
  payload :=
    case2AllPivotActualWidthStoppedProducedBranchPayload_of_currentCenterSourceInput
      input Cterminal Fterminal hguard chartEquiv
  payload_state := rfl

/-- Package the terminal-last row-exhausted fixed-current-center payload as
branch-indexed current-center data. -/
def of_rowExhaustedTerminalLast
    {κ : Fin (L + 1) → Type}
    [∀ i, Finite (κ i)]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) ℝ)
    (hguard : case2AllPivotRowExhaustedTerminalLastGuard s)
    (Cterminal :
      ℕ → κ (sourceLayerIndex L (s.S + 2)
        (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
        (Nat.succ_le_succ (le_of_eq hguard.2))) → ℝ)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    Case2AllPivotCurrentCenterProducedPayload s hguard.1.1 where
  chartEquiv := chartEquiv
  payload :=
    case2AllPivotRowExhaustedTerminalLastProducedBranchPayload_of_currentCenterSourceInput
      input Ctail hguard Cterminal chartEquiv
  payload_state := rfl

/-- Package the source-suffix row-exhausted fixed-current-center payload as
branch-indexed current-center data. -/
def of_rowExhaustedSourceSuffix
    {κ : Fin (L + 1) → Type}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) ℝ)
    (hguard : case2AllPivotRowExhaustedSourceSuffixGuard s)
    (Csuffix :
      ℕ → κ (sourceLayerIndex L (s.S + 2)
        (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
        (Nat.succ_le_succ hguard.2)) → ℝ)
    (chartEquiv :
      Fin (case2ResidualBlockPivotEntries n s.S s.J).card ≃
        (case2ResidualBlockPivotEntries n s.S s.J : Type)) :
    Case2AllPivotCurrentCenterProducedPayload s hguard.1.1 where
  chartEquiv := chartEquiv
  payload :=
    case2AllPivotRowExhaustedSourceSuffixProducedBranchPayload_of_currentCenterSourceInput
      input Ctail hguard Csuffix chartEquiv
  payload_state := rfl

end Case2AllPivotCurrentCenterProducedPayload

/-- Branch-indexed current-center produced payload data for the displayed
all-pivot Case 2 subcases.

The row-exhausted payload APIs remain split into terminal-last and
source-suffix packages.  This record deliberately does not merge them into the
single `rowExhaustedStoppedPayload` required by
`SelectedEntryAtlasProducedBranchData`, and it deliberately has no conversion
to that fixed-context producer record. -/
structure Case2AllPivotBranchIndexedProducedPayloadData
    (L : ℕ) (n : ℕ → ℕ) where
  continuingPayload :
    ∀ (s : AoyagiRecurrenceBranchState L n ℝ)
      (h : case2AllPivotContinuingGuard s),
      Case2AllPivotCurrentCenterProducedPayload s h.1
  actualWidthStoppedPayload :
    ∀ (s : AoyagiRecurrenceBranchState L n ℝ)
      (h : case2AllPivotActualWidthStoppedGuard s),
      Case2AllPivotCurrentCenterProducedPayload s h.1
  rowExhaustedTerminalLastPayload :
    ∀ (s : AoyagiRecurrenceBranchState L n ℝ)
      (h : case2AllPivotRowExhaustedTerminalLastGuard s),
      Case2AllPivotCurrentCenterProducedPayload s h.1.1
  rowExhaustedSourceSuffixPayload :
    ∀ (s : AoyagiRecurrenceBranchState L n ℝ)
      (h : case2AllPivotRowExhaustedSourceSuffixGuard s),
      Case2AllPivotCurrentCenterProducedPayload s h.1.1

namespace Case2AllPivotBranchIndexedProducedPayloadData

variable {L : ℕ} {n : ℕ → ℕ}
variable (data : Case2AllPivotBranchIndexedProducedPayloadData L n)
variable {s : AoyagiRecurrenceBranchState L n ℝ}

@[simp]
theorem continuingPayload_branchState
    (h : case2AllPivotContinuingGuard s) :
    ((data.continuingPayload s h).payload).branchState = s :=
  (data.continuingPayload s h).payload_state

@[simp]
theorem actualWidthStoppedPayload_branchState
    (h : case2AllPivotActualWidthStoppedGuard s) :
    ((data.actualWidthStoppedPayload s h).payload).branchState = s :=
  (data.actualWidthStoppedPayload s h).payload_state

@[simp]
theorem rowExhaustedTerminalLastPayload_branchState
    (h : case2AllPivotRowExhaustedTerminalLastGuard s) :
    ((data.rowExhaustedTerminalLastPayload s h).payload).branchState = s :=
  (data.rowExhaustedTerminalLastPayload s h).payload_state

@[simp]
theorem rowExhaustedSourceSuffixPayload_branchState
    (h : case2AllPivotRowExhaustedSourceSuffixGuard s) :
    ((data.rowExhaustedSourceSuffixPayload s h).payload).branchState = s :=
  (data.rowExhaustedSourceSuffixPayload s h).payload_state

end Case2AllPivotBranchIndexedProducedPayloadData

end Aoyagi
end DLN
end DLNFibre
