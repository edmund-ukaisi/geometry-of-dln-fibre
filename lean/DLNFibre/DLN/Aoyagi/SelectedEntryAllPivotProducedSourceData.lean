import DLNFibre.DLN.Aoyagi.SelectedEntryCase2ProducedGuards

/-!
# Finite Case 2 source data for all-pivot producer payloads

This file records the finite source-data layer immediately below
`SelectedEntryAtlasProducedBranchData`.  It names active-refined all-pivot Case
2 guards and packages branch-specific source data using the existing displayed
Case 2 frontier payloads from `BlowupArithmetic`.

The records here are not analytic producer payloads: they do not contain
all-pivot chart indices, chart points, chart-domain membership, source-domain
membership, or center-alignment data.  Consequently this file does not
instantiate `SelectedEntryAtlasProducedBranchData`.

The recurrence data in this file is valued in the same ring `R` as the
displayed source chart.  A generic `AoyagiRecurrenceBranchState L n α`
producer must either specialize to this value type or provide an explicit
transport from displayed pivot values into `α`.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

open Case2DisplayedSuppliedChartFamilyBoundary

universe u υ τ

/-- All-pivot source-production continuing guard: displayed Case 2 active
pivot plus same-stage next pivot. -/
def case2AllPivotContinuingGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  AoyagiRecurrenceBranchState.case2DisplayedActiveContinuingGuard s

/-- All-pivot source-production actual-width stopped guard: displayed Case 2
active pivot plus actual next-width exhaustion. -/
def case2AllPivotActualWidthStoppedGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  AoyagiRecurrenceBranchState.case2DisplayedActiveActualWidthStoppedGuard s

/-- All-pivot source-production row-exhausted stopped guard: displayed Case 2
active pivot plus current-prefix row exhaustion. -/
def case2AllPivotRowExhaustedStoppedGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  AoyagiRecurrenceBranchState.case2DisplayedActiveRowExhaustedStoppedGuard s

/-- Row-exhausted source-suffix guard.

The transported source-suffix payload is available only when there is a next
source layer to carry the suffix.  This is stronger than the semantic
row-exhausted stopped guard used in the active frontier split. -/
def case2AllPivotRowExhaustedSourceSuffixGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  case2AllPivotRowExhaustedStoppedGuard s ∧ s.S + 1 ≤ L

/-- Row-exhausted terminal-last guard.

This is the no-suffix terminal-last row-exhausted subcase.  It is separate
from the source-suffix row-exhausted package because the existing terminal-last
frontier payload consumes the suffix through `S + 1 = L`. -/
def case2AllPivotRowExhaustedTerminalLastGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  case2AllPivotRowExhaustedStoppedGuard s ∧ s.S + 1 = L

/-- The active-refined all-pivot guards cover the displayed Case 2 active
region. -/
theorem case2AllPivotGuards_complete
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α)
    (hactive : AoyagiRecurrenceBranchState.case2DisplayedActiveGuard s) :
    case2AllPivotContinuingGuard s ∨
      case2AllPivotActualWidthStoppedGuard s ∨
        case2AllPivotRowExhaustedStoppedGuard s := by
  simpa [case2AllPivotContinuingGuard,
    case2AllPivotActualWidthStoppedGuard,
    case2AllPivotRowExhaustedStoppedGuard] using
      AoyagiRecurrenceBranchState.case2Displayed_activeFrontier_guards_complete
        s hactive

/-- A source-suffix row-exhausted guard forgets to the semantic stopped guard. -/
theorem case2AllPivotRowExhaustedStoppedGuard_of_sourceSuffixGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {s : AoyagiRecurrenceBranchState L n α}
    (h : case2AllPivotRowExhaustedSourceSuffixGuard s) :
    case2AllPivotRowExhaustedStoppedGuard s :=
  h.1

/-- A terminal-last row-exhausted guard forgets to the semantic stopped guard. -/
theorem case2AllPivotRowExhaustedStoppedGuard_of_terminalLastGuard
    {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    {s : AoyagiRecurrenceBranchState L n α}
    (h : case2AllPivotRowExhaustedTerminalLastGuard s) :
    case2AllPivotRowExhaustedStoppedGuard s :=
  h.1

/-- Shared displayed source-chart input for a Case 2 all-pivot branch state.

This is finite source data only.  It is not a chart-domain point in the
selected-entry analytic atlas. -/
structure Case2AllPivotDisplayedSourceInput
    {R : Type u} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiRecurrenceBranchState L n R)
    (t : ℕ → ℕ → ℕ → ℤ)
    (numerator leastValue : ℕ → ℕ → ℤ) where
  u : R
  residual : ℕ × ℕ → R
  active : AoyagiRecurrenceBranchState.case2DisplayedActiveGuard s
  exponentPre :
    IntroducedLabelExponentCertificates L n s.S s.J t numerator leastValue
  levelInv :
    IntroducedLabelLevelInvariants L n s.S s.J s.recurrence.level leastValue
  leastValueGap :
    case2IntroducedLabelLeastValueGap L n s.S s.J leastValue

namespace Case2AllPivotDisplayedSourceInput

variable {R : Type u} [CommRing R]
variable {L : ℕ} {n : ℕ → ℕ}
variable {s : AoyagiRecurrenceBranchState L n R}
variable {t : ℕ → ℕ → ℕ → ℤ}
variable {numerator leastValue : ℕ → ℕ → ℤ}

/-- The selected pivot value produced by the displayed Case 2 source chart. -/
def pivotValue
    (input :
      Case2AllPivotDisplayedSourceInput s t numerator leastValue) : R :=
  case2DisplayedSourceChartMap n s.stage_pos input.active input.u
    input.residual (s.J + 1, s.J + 1)

/-- The concrete same-stage recurrence post-state attached to the displayed
Case 2 source chart. -/
def continuingRecurrence
    (input :
      Case2AllPivotDisplayedSourceInput s t numerator leastValue) :
    IntroducedLabelRecurrenceState L n s.S (s.J + 1) R :=
  s.recurrence.case2Succ input.pivotValue

/-- The concrete stage-relabelled recurrence state attached to an actual-width
stopped displayed Case 2 source chart. -/
def actualWidthRelabelRecurrence
    (input :
      Case2AllPivotDisplayedSourceInput s t numerator leastValue) :
    IntroducedLabelRecurrenceState L n (s.S + 1) 0 R :=
  input.continuingRecurrence.stageRelabelSuccZero

end Case2AllPivotDisplayedSourceInput

/-- Continuing branch finite source data for the all-pivot producer frontier.

This packages the existing weighted successor-following frontier payload and
the concrete same-stage child recurrence.  It is still below
`SelectedEntryProducedBranchPayload`: no analytic chart token or chart point is
constructed here. -/
structure Case2AllPivotContinuingProducedSourceData
    {τ R : Type u} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n R}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (C : ℕ → τ → R) where
  guard : case2AllPivotContinuingGuard s
  frontier :
    ContinuingWeightedSuccFollowingFrontierPayload
      L n s.S s.J t numerator leastValue s.recurrence input.u
      input.residual s.stage_pos input.active C
  childRecurrence :
    IntroducedLabelRecurrenceState L n s.S (s.J + 1) R
  childRecurrence_eq :
    childRecurrence = input.continuingRecurrence

namespace Case2AllPivotContinuingProducedSourceData

variable {τ R : Type u} [CommRing R]
variable {L : ℕ} {n : ℕ → ℕ}
variable {s : AoyagiRecurrenceBranchState L n R}
variable {t : ℕ → ℕ → ℕ → ℤ}
variable {numerator leastValue : ℕ → ℕ → ℤ}
variable {input : Case2AllPivotDisplayedSourceInput s t numerator leastValue}
variable {C : ℕ → τ → R}

/-- Construct continuing source data from the displayed source-chart input and
the active-continuing guard. -/
def of_sourceInput
    (hguard : case2AllPivotContinuingGuard s) :
    Case2AllPivotContinuingProducedSourceData input C := by
  refine
    { guard := hguard
      frontier := ?_
      childRecurrence := input.continuingRecurrence
      childRecurrence_eq := rfl }
  exact
    sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal_withoutChartFamily
      s.recurrence input.u input.residual s.stage_pos s.stage_le
      input.active
      (by
        simpa [case2AllPivotContinuingGuard,
          AoyagiRecurrenceBranchState.case2DisplayedActiveContinuingGuard,
          AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard,
          AoyagiRecurrenceBranchState.toIntroducedState] using hguard.2)
      input.exponentPre input.levelInv input.leastValueGap C

/-- The continuing source data's child recurrence gives recurrence-aware
progress. -/
theorem child_progress
    (data : Case2AllPivotContinuingProducedSourceData input C) :
    AoyagiRecurrenceBranchState.progressStep L n R
      (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence
        s data.childRecurrence)
      s := by
  rw [data.childRecurrence_eq]
  exact
    AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_activeContinuingGuard
      s input.continuingRecurrence data.guard

end Case2AllPivotContinuingProducedSourceData

/-- Actual-width stopped finite source data for the all-pivot producer
frontier.

The payload is the existing actual-width source-chart frontier package, with
the stage-relabelled recurrence state recorded explicitly. -/
structure Case2AllPivotActualWidthStoppedProducedSourceData
    {υ τ R : Type u} [CommRing R] [Fintype τ]
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n R}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (C : ℕ → τ → R) (F : Matrix τ υ R) where
  guard : case2AllPivotActualWidthStoppedGuard s
  frontier :
    ActualWidthSourceChartFrontierPayload
      L n s.S s.J t numerator leastValue s.recurrence input.u
      input.residual s.stage_pos input.active C F
  terminalRecurrence :
    IntroducedLabelRecurrenceState L n (s.S + 1) 0 R
  terminalRecurrence_eq :
    terminalRecurrence = input.actualWidthRelabelRecurrence

namespace Case2AllPivotActualWidthStoppedProducedSourceData

variable {υ τ R : Type u} [CommRing R] [Fintype τ]
variable {L : ℕ} {n : ℕ → ℕ}
variable {s : AoyagiRecurrenceBranchState L n R}
variable {t : ℕ → ℕ → ℕ → ℤ}
variable {numerator leastValue : ℕ → ℕ → ℤ}
variable {input : Case2AllPivotDisplayedSourceInput s t numerator leastValue}
variable {C : ℕ → τ → R} {F : Matrix τ υ R}

/-- Construct actual-width stopped source data from the displayed source-chart
input and active actual-width guard. -/
def of_sourceInput
    (hguard : case2AllPivotActualWidthStoppedGuard s) :
    Case2AllPivotActualWidthStoppedProducedSourceData input C F := by
  let frontier :
      SourceChartFrontierBoundaryPackages.{u, u, u, u, u, u, u}
        R L n s.S s.J t numerator leastValue
        s.recurrence input.u input.residual s.stage_pos input.active :=
    sourceChartMap_frontierBoundaryPackages_withoutChartFamily
      s.recurrence input.u input.residual s.stage_pos s.stage_le
      input.active input.exponentPre input.levelInv input.leastValueGap
  refine
    { guard := hguard
      frontier := ?_
      terminalRecurrence := input.actualWidthRelabelRecurrence
      terminalRecurrence_eq := rfl }
  exact
    frontier.actualWidthStopped C F (by
      simpa [case2AllPivotActualWidthStoppedGuard,
        AoyagiRecurrenceBranchState.case2DisplayedActiveActualWidthStoppedGuard,
        AoyagiIntroducedLabelBranchState.case2DisplayedActualWidthStoppedGuard,
        AoyagiRecurrenceBranchState.toIntroducedState] using hguard.2)

end Case2AllPivotActualWidthStoppedProducedSourceData

/-- Row-exhausted terminal-last finite source data for the all-pivot producer
frontier.

This is the no-suffix row-exhausted subcase `s.S + 1 = L`.  It keeps the
terminal-last transported-prefix payload separate from the source-suffix row
payload and from actual-width stopping. -/
structure Case2AllPivotRowExhaustedTerminalLastProducedSourceData
    {R : Type u} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n R}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (κ : Fin (L + 1) → Type u)
    [∀ i, Finite (κ i)]
    (hLast : s.S + 1 = L)
    (C : ℕ → κ (sourceLayerIndex L (s.S + 2)
      (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
      (Nat.succ_le_succ (le_of_eq hLast))) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) where
  guard : case2AllPivotRowExhaustedTerminalLastGuard s
  frontier :
    RowExhaustedTerminalLastSourceChartFrontierPayload
      L n s.S s.J s.recurrence input.u input.residual s.stage_pos
      input.active
      (by
        simpa [case2AllPivotRowExhaustedStoppedGuard,
          case2AllPivotRowExhaustedTerminalLastGuard,
          AoyagiRecurrenceBranchState.case2DisplayedActiveRowExhaustedStoppedGuard,
          AoyagiIntroducedLabelBranchState.case2DisplayedRowExhaustedStoppedGuard,
          AoyagiRecurrenceBranchState.toIntroducedState] using guard.1.2)
      κ (le_of_eq hLast) C

namespace Case2AllPivotRowExhaustedTerminalLastProducedSourceData

variable {R : Type u} [CommRing R]
variable {L : ℕ} {n : ℕ → ℕ}
variable {s : AoyagiRecurrenceBranchState L n R}
variable {t : ℕ → ℕ → ℕ → ℤ}
variable {numerator leastValue : ℕ → ℕ → ℤ}
variable {input : Case2AllPivotDisplayedSourceInput s t numerator leastValue}
variable {κ : Fin (L + 1) → Type u}
variable [∀ i, Finite (κ i)]
variable {Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R}

/-- Construct terminal-last row-exhausted source data from the displayed
source-chart input and the terminal-last row-exhausted guard. -/
def of_sourceInput
    (hguard : case2AllPivotRowExhaustedTerminalLastGuard s)
    (C : ℕ → κ (sourceLayerIndex L (s.S + 2)
      (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
      (Nat.succ_le_succ (le_of_eq hguard.2))) → R) :
    Case2AllPivotRowExhaustedTerminalLastProducedSourceData
      input κ hguard.2 C Ctail := by
  let frontier :
      SourceChartFrontierBoundaryPackages.{u, u, u, u, u, u, u}
        R L n s.S s.J t numerator leastValue
        s.recurrence input.u input.residual s.stage_pos input.active :=
    sourceChartMap_frontierBoundaryPackages_withoutChartFamily
      s.recurrence input.u input.residual s.stage_pos s.stage_le
      input.active input.exponentPre input.levelInv input.leastValueGap
  refine
    { guard := hguard
      frontier := ?_ }
  exact
    frontier.rowExhaustedStopped
      κ (le_of_eq hguard.2) hguard.2 C Ctail (by
        simpa [case2AllPivotRowExhaustedStoppedGuard,
          case2AllPivotRowExhaustedTerminalLastGuard,
          AoyagiRecurrenceBranchState.case2DisplayedActiveRowExhaustedStoppedGuard,
          AoyagiIntroducedLabelBranchState.case2DisplayedRowExhaustedStoppedGuard,
          AoyagiRecurrenceBranchState.toIntroducedState] using hguard.1.2)

end Case2AllPivotRowExhaustedTerminalLastProducedSourceData

/-- Row-exhausted stopped finite source data for the all-pivot producer
frontier.

This is the source-suffix subcase of row exhaustion.  It keeps row exhaustion
separate from actual-width stopping and requires a next source layer
`s.S + 1 ≤ L`, because the transported-prefix source-suffix payload has that
domain. -/
structure Case2AllPivotRowExhaustedStoppedProducedSourceData
    {R : Type u} [CommRing R]
    {L : ℕ} {n : ℕ → ℕ}
    {s : AoyagiRecurrenceBranchState L n R}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    (input : Case2AllPivotDisplayedSourceInput s t numerator leastValue)
    (κ : Fin (L + 1) → Type u)
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (hSuffix : s.S + 1 ≤ L)
    (C : ℕ → κ (sourceLayerIndex L (s.S + 2)
      (Nat.succ_le_succ (Nat.zero_le (s.S + 1))) (Nat.succ_le_succ hSuffix)) → R)
    (Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R) where
  guard : case2AllPivotRowExhaustedSourceSuffixGuard s
  frontier :
    RowExhaustedSourceSuffixTransportedPrefixPayload
      L n s.S s.J s.recurrence input.u input.residual s.stage_pos
      input.active
      (by
        simpa [case2AllPivotRowExhaustedStoppedGuard,
          case2AllPivotRowExhaustedSourceSuffixGuard,
          AoyagiRecurrenceBranchState.case2DisplayedActiveRowExhaustedStoppedGuard,
          AoyagiIntroducedLabelBranchState.case2DisplayedRowExhaustedStoppedGuard,
          AoyagiRecurrenceBranchState.toIntroducedState] using guard.1.2)
      κ hSuffix C Ctail

namespace Case2AllPivotRowExhaustedStoppedProducedSourceData

variable {R : Type u} [CommRing R]
variable {L : ℕ} {n : ℕ → ℕ}
variable {s : AoyagiRecurrenceBranchState L n R}
variable {t : ℕ → ℕ → ℕ → ℤ}
variable {numerator leastValue : ℕ → ℕ → ℤ}
variable {input : Case2AllPivotDisplayedSourceInput s t numerator leastValue}
variable {κ : Fin (L + 1) → Type u}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable {Ctail : ∀ p : Fin L, Matrix (κ p.castSucc) (κ p.succ) R}

/-- Construct row-exhausted stopped source data from the displayed source-chart
input and the source-suffix row-exhausted guard. -/
def of_sourceInput
    (hguard : case2AllPivotRowExhaustedSourceSuffixGuard s)
    (C : ℕ → κ (sourceLayerIndex L (s.S + 2)
      (Nat.succ_le_succ (Nat.zero_le (s.S + 1)))
      (Nat.succ_le_succ hguard.2)) → R) :
    Case2AllPivotRowExhaustedStoppedProducedSourceData
      input κ hguard.2 C Ctail := by
  let frontier :
      SourceChartFrontierBoundaryPackages.{u, u, u, u, u, u, u}
        R L n s.S s.J t numerator leastValue
        s.recurrence input.u input.residual s.stage_pos input.active :=
    sourceChartMap_frontierBoundaryPackages_withoutChartFamily
      s.recurrence input.u input.residual s.stage_pos s.stage_le
      input.active input.exponentPre input.levelInv input.leastValueGap
  refine
    { guard := hguard
      frontier := ?_ }
  exact
    frontier.rowExhaustedSourceSuffix κ hguard.2 C Ctail (by
      simpa [case2AllPivotRowExhaustedStoppedGuard,
        case2AllPivotRowExhaustedSourceSuffixGuard,
        AoyagiRecurrenceBranchState.case2DisplayedActiveRowExhaustedStoppedGuard,
        AoyagiIntroducedLabelBranchState.case2DisplayedRowExhaustedStoppedGuard,
        AoyagiRecurrenceBranchState.toIntroducedState] using hguard.1.2)

end Case2AllPivotRowExhaustedStoppedProducedSourceData

end Aoyagi
end DLN
end DLNFibre
