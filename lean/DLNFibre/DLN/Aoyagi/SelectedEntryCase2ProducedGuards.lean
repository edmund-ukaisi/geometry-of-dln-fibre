import DLNFibre.DLN.Aoyagi.SelectedEntryBranchProgressBridge

/-!
# Active displayed Case 2 guards for selected-entry source production

The selected-entry producer's branch payload functions are total over their
guards.  The displayed stopped equalities from the finite frontier are only
source-production domains after the displayed Case 2 pivot is active.  This
file names the active-refined guards and proves they cover the active region.

It does not construct source-production payloads, analytic chart domains,
transition regularity, Jacobian/volume compatibility, normal crossings, pole
order, or RLCT data.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiIntroducedLabelBranchState

/-- Active-refined displayed Case 2 continuing guard for source production. -/
def case2DisplayedActiveContinuingGuard {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) : Prop :=
  case2DisplayedActiveGuard s ∧ case2DisplayedContinuingGuard s

/-- Active-refined displayed Case 2 actual-width stopped guard for source
production. -/
def case2DisplayedActiveActualWidthStoppedGuard {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) : Prop :=
  case2DisplayedActiveGuard s ∧ case2DisplayedActualWidthStoppedGuard s

/-- Active-refined displayed Case 2 row-exhausted stopped guard for source
production. -/
def case2DisplayedActiveRowExhaustedStoppedGuard {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) : Prop :=
  case2DisplayedActiveGuard s ∧ case2DisplayedRowExhaustedStoppedGuard s

/-- On the active displayed Case 2 region, the active-refined source-production
guards cover the finite frontier. -/
theorem case2Displayed_activeFrontier_guards_complete
    {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n)
    (hactive : case2DisplayedActiveGuard s) :
    case2DisplayedActiveContinuingGuard s ∨
      case2DisplayedActiveActualWidthStoppedGuard s ∨
        case2DisplayedActiveRowExhaustedStoppedGuard s := by
  rcases case2Displayed_frontier_guards_complete s hactive with
    hnext | hstopped
  · exact Or.inl ⟨hactive, hnext⟩
  · rcases hstopped with hactual | hrow
    · exact Or.inr (Or.inl ⟨hactive, hactual⟩)
    · exact Or.inr (Or.inr ⟨hactive, hrow⟩)

/-- Active-continuing source-production guard implies the displayed continuing
guard. -/
theorem case2DisplayedContinuingGuard_of_activeContinuingGuard
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiIntroducedLabelBranchState L n}
    (h : case2DisplayedActiveContinuingGuard s) :
    case2DisplayedContinuingGuard s :=
  h.2

/-- Active-continuing source-production guard gives the same-stage progress
step. -/
theorem case2SameStageChild_progress_of_activeContinuingGuard
    {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n)
    (h : case2DisplayedActiveContinuingGuard s) :
    progressStep L n (case2SameStageChild s) s :=
  case2SameStageChild_progress_of_prefixBound s h.1

end AoyagiIntroducedLabelBranchState

namespace AoyagiRecurrenceBranchState

/-- Active-refined displayed Case 2 continuing guard for recurrence-aware
source production. -/
def case2DisplayedActiveContinuingGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  case2DisplayedActiveGuard s ∧
    AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard
      s.toIntroducedState

/-- Active-refined displayed Case 2 actual-width stopped guard for
recurrence-aware source production. -/
def case2DisplayedActiveActualWidthStoppedGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  case2DisplayedActiveGuard s ∧
    AoyagiIntroducedLabelBranchState.case2DisplayedActualWidthStoppedGuard
      s.toIntroducedState

/-- Active-refined displayed Case 2 row-exhausted stopped guard for
recurrence-aware source production. -/
def case2DisplayedActiveRowExhaustedStoppedGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  case2DisplayedActiveGuard s ∧
    AoyagiIntroducedLabelBranchState.case2DisplayedRowExhaustedStoppedGuard
      s.toIntroducedState

/-- On the active recurrence-aware displayed Case 2 region, the active-refined
source-production guards cover the finite frontier. -/
theorem case2Displayed_activeFrontier_guards_complete
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (hactive : case2DisplayedActiveGuard s) :
    case2DisplayedActiveContinuingGuard s ∨
      case2DisplayedActiveActualWidthStoppedGuard s ∨
        case2DisplayedActiveRowExhaustedStoppedGuard s := by
  have hactiveIntro :
      AoyagiIntroducedLabelBranchState.case2DisplayedActiveGuard
        s.toIntroducedState := by
    simpa [case2DisplayedActiveGuard,
      AoyagiIntroducedLabelBranchState.case2DisplayedActiveGuard,
      toIntroducedState] using hactive
  rcases
      AoyagiIntroducedLabelBranchState.case2Displayed_activeFrontier_guards_complete
        s.toIntroducedState hactiveIntro with
    hnext | hstopped
  · exact Or.inl ⟨hactive, hnext.2⟩
  · rcases hstopped with hactual | hrow
    · exact Or.inr (Or.inl ⟨hactive, hactual.2⟩)
    · exact Or.inr (Or.inr ⟨hactive, hrow.2⟩)

/-- Active-continuing recurrence-aware source-production guard implies the
displayed continuing guard on the support-only state. -/
theorem case2DisplayedContinuingGuard_of_activeContinuingGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {s : AoyagiRecurrenceBranchState L n α}
    (h : case2DisplayedActiveContinuingGuard s) :
    AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard
      s.toIntroducedState :=
  h.2

/-- Active-continuing source-production guard gives recurrence-aware
same-stage progress for any supplied child recurrence data. -/
theorem sameStageChildWithRecurrence_progress_of_activeContinuingGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (recurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) α)
    (h : case2DisplayedActiveContinuingGuard s) :
    progressStep L n α (sameStageChildWithRecurrence s recurrence) s :=
  sameStageChildWithRecurrence_progress_of_prefixBound s recurrence h.1

end AoyagiRecurrenceBranchState

end Aoyagi
end DLN
end DLNFibre
