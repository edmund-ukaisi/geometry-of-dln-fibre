import DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasProducer
import DLNFibre.DLN.Aoyagi.BlowupBranchProgress

/-!
# Selected-entry branch progress bridge

This file connects the supplied selected-entry analytic-atlas branch interface
to the introduced-label and recurrence-aware progress kernels.

It does not construct `SelectedEntryAtlasProducedBranchData`, source payloads,
terminal payloads, chart production, normal crossings, pole order, or RLCT
data.  It only supplies well-founded termination relations from finite progress
measures and progress-data bridges whose continuing children are supplied or
finite bookkeeping states.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

universe uAtlas

/-- Branch-termination data supplied by the finite introduced-label progress
relation.

The initial state is `(1,0)`, so this constructor requires `1 <= L`.  This is
only a termination relation on branch states; it does not construct branch
source-production data. -/
def selectedEntryIntroducedLabelBranchTerminationData
    {Param R : Type*} [CommMonoid R]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R)
    (L : ℕ) (n : ℕ → ℕ) (hL : 1 ≤ L) :
    SelectedEntryBranchTerminationData C (AoyagiIntroducedLabelBranchState L n) where
  step := AoyagiIntroducedLabelBranchState.progressStep L n
  step_wellFounded := AoyagiIntroducedLabelBranchState.progressStep_wellFounded L n
  initial := ⟨1, 0, Nat.le_refl 1, hL⟩

/-- Branch-termination data supplied by the finite recurrence-aware progress
relation.

The initial state is `(1,0)` with supplied initial recurrence data.  This is
only a termination relation on branch states; it does not construct recurrence
data, branch guards, or source-production payloads. -/
def selectedEntryRecurrenceBranchTerminationData
    {Param R : Type*} [CommMonoid R]
    (C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R)
    (L : ℕ) (n : ℕ → ℕ) (α : Type*) (hL : 1 ≤ L)
    (initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 α) :
    SelectedEntryBranchTerminationData C (AoyagiRecurrenceBranchState L n α) where
  step := AoyagiRecurrenceBranchState.progressStep L n α
  step_wellFounded := AoyagiRecurrenceBranchState.progressStep_wellFounded L n α
  initial := ⟨1, 0, Nat.le_refl 1, hL, initialRecurrence⟩

namespace AoyagiIntroducedLabelBranchState

/-- Displayed Case 2 active branch guard: the selected pivot `(J+1,J+1)` is
within the current residual block. -/
def case2DisplayedActiveGuard {L : ℕ} {n : ℕ → ℕ}
    (s : AoyagiIntroducedLabelBranchState L n) : Prop :=
  s.J + 1 ≤ prefixMinNat n (s.S + 1)

end AoyagiIntroducedLabelBranchState

namespace AoyagiRecurrenceBranchState

/-- Displayed Case 2 active branch guard on recurrence-aware branch states:
the selected pivot `(J+1,J+1)` is within the current residual block. -/
def case2DisplayedActiveGuard {L : ℕ} {n : ℕ → ℕ} {α : Type*}
    (s : AoyagiRecurrenceBranchState L n α) : Prop :=
  s.J + 1 ≤ prefixMinNat n (s.S + 1)

end AoyagiRecurrenceBranchState

/-- Displayed Case 2 branch-progress data from the pivot-validity bound.

This assumes the supplied source-production guards cover the displayed active
guard and that every supplied continuing guard satisfies the displayed
pivot-validity bound.  It constructs no source-production payload. -/
def selectedEntryCase2DisplayedPrefixBoundBranchProgressData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    {ctx : SelectedEntryAnalyticAtlasContext C}
    {L : ℕ} {n : ℕ → ℕ} {hL : 1 ≤ L}
    (sourceProduction :
      SelectedEntryAtlasProducedBranchData ctx
        (AoyagiIntroducedLabelBranchState L n))
    (hcomplete :
      ∀ s : AoyagiIntroducedLabelBranchState L n,
        AoyagiIntroducedLabelBranchState.case2DisplayedActiveGuard s →
          sourceProduction.continuingGuard s ∨
            sourceProduction.actualWidthStoppedGuard s ∨
              sourceProduction.rowExhaustedStoppedGuard s)
    (hbound :
      ∀ (s : AoyagiIntroducedLabelBranchState L n)
        (_h : sourceProduction.continuingGuard s),
        s.J + 1 ≤ prefixMinNat n (s.S + 1)) :
    SelectedEntryAtlasBranchProgressData sourceProduction
      (selectedEntryIntroducedLabelBranchTerminationData C L n hL) where
  activeGuard := AoyagiIntroducedLabelBranchState.case2DisplayedActiveGuard
  guards_complete := hcomplete
  continuingChild :=
    fun s _ ↦ AoyagiIntroducedLabelBranchState.case2SameStageChild s
  continuing_child_step := by
    intro s h
    simpa [selectedEntryIntroducedLabelBranchTerminationData] using
      AoyagiIntroducedLabelBranchState.case2SameStageChild_progress_of_prefixBound
        s (hbound s h)

/-- Displayed Case 2 branch-progress data from the displayed continuing guard.

This assumes the supplied source-production guards cover the displayed active
guard and that every supplied continuing guard implies Aoyagi's displayed Case
2 continuing guard. -/
def selectedEntryCase2DisplayedContinuingBranchProgressData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    {ctx : SelectedEntryAnalyticAtlasContext C}
    {L : ℕ} {n : ℕ → ℕ} {hL : 1 ≤ L}
    (sourceProduction :
      SelectedEntryAtlasProducedBranchData ctx
        (AoyagiIntroducedLabelBranchState L n))
    (hcomplete :
      ∀ s : AoyagiIntroducedLabelBranchState L n,
        AoyagiIntroducedLabelBranchState.case2DisplayedActiveGuard s →
          sourceProduction.continuingGuard s ∨
            sourceProduction.actualWidthStoppedGuard s ∨
              sourceProduction.rowExhaustedStoppedGuard s)
    (hguard :
      ∀ (s : AoyagiIntroducedLabelBranchState L n)
        (_h : sourceProduction.continuingGuard s),
        AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard s) :
    SelectedEntryAtlasBranchProgressData sourceProduction
      (selectedEntryIntroducedLabelBranchTerminationData C L n hL) :=
  selectedEntryCase2DisplayedPrefixBoundBranchProgressData
    (C := C) (ctx := ctx) (L := L) (n := n) (hL := hL)
    sourceProduction hcomplete (by
      intro s h
      have hnext := hguard s h
      dsimp [AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard] at hnext
      omega)

/-- Recurrence-aware displayed Case 2 branch-progress data from the
pivot-validity bound.

This is the recurrence-state analogue of
`selectedEntryCase2DisplayedPrefixBoundBranchProgressData`.  It requires
explicit child recurrence data for continuing branches; the bridge constructs
no recurrence data or source-production payload. -/
def selectedEntryCase2DisplayedRecurrencePrefixBoundBranchProgressData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    {ctx : SelectedEntryAnalyticAtlasContext C}
    {L : ℕ} {n : ℕ → ℕ} {α : Type*} {hL : 1 ≤ L}
    (initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 α)
    (sourceProduction :
      SelectedEntryAtlasProducedBranchData ctx
        (AoyagiRecurrenceBranchState L n α))
    (childRecurrence :
      ∀ (s : AoyagiRecurrenceBranchState L n α)
        (_h : sourceProduction.continuingGuard s),
        IntroducedLabelRecurrenceState L n s.S (s.J + 1) α)
    (hcomplete :
      ∀ s : AoyagiRecurrenceBranchState L n α,
        AoyagiRecurrenceBranchState.case2DisplayedActiveGuard s →
          sourceProduction.continuingGuard s ∨
            sourceProduction.actualWidthStoppedGuard s ∨
              sourceProduction.rowExhaustedStoppedGuard s)
    (hbound :
      ∀ (s : AoyagiRecurrenceBranchState L n α)
        (_h : sourceProduction.continuingGuard s),
        s.J + 1 ≤ prefixMinNat n (s.S + 1)) :
    SelectedEntryAtlasBranchProgressData sourceProduction
      (selectedEntryRecurrenceBranchTerminationData
        C L n α hL initialRecurrence) where
  activeGuard := AoyagiRecurrenceBranchState.case2DisplayedActiveGuard
  guards_complete := hcomplete
  continuingChild :=
    fun s h ↦
      AoyagiRecurrenceBranchState.sameStageChildWithRecurrence s
        (childRecurrence s h)
  continuing_child_step := by
    intro s h
    simpa [selectedEntryRecurrenceBranchTerminationData] using
      AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_prefixBound
        s (childRecurrence s h) (hbound s h)

/-- Recurrence-aware displayed Case 2 branch-progress data from the displayed
continuing guard.

This assumes supplied child recurrence data for continuing branches and that
each continuing branch satisfies Aoyagi's displayed Case 2 continuing guard. -/
def selectedEntryCase2DisplayedRecurrenceContinuingBranchProgressData
    {Param R : Type*} [CommMonoid R] [TopologicalSpace Param]
    {C : AoyagiNormalCrossingChartCertificate.{uAtlas} Param R}
    {ctx : SelectedEntryAnalyticAtlasContext C}
    {L : ℕ} {n : ℕ → ℕ} {α : Type*} {hL : 1 ≤ L}
    (initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 α)
    (sourceProduction :
      SelectedEntryAtlasProducedBranchData ctx
        (AoyagiRecurrenceBranchState L n α))
    (childRecurrence :
      ∀ (s : AoyagiRecurrenceBranchState L n α)
        (_h : sourceProduction.continuingGuard s),
        IntroducedLabelRecurrenceState L n s.S (s.J + 1) α)
    (hcomplete :
      ∀ s : AoyagiRecurrenceBranchState L n α,
        AoyagiRecurrenceBranchState.case2DisplayedActiveGuard s →
          sourceProduction.continuingGuard s ∨
            sourceProduction.actualWidthStoppedGuard s ∨
              sourceProduction.rowExhaustedStoppedGuard s)
    (hguard :
      ∀ (s : AoyagiRecurrenceBranchState L n α)
        (_h : sourceProduction.continuingGuard s),
        AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard
          s.toIntroducedState) :
    SelectedEntryAtlasBranchProgressData sourceProduction
      (selectedEntryRecurrenceBranchTerminationData
        C L n α hL initialRecurrence) :=
  selectedEntryCase2DisplayedRecurrencePrefixBoundBranchProgressData
    (C := C) (ctx := ctx) (L := L) (n := n) (α := α) (hL := hL)
    initialRecurrence sourceProduction childRecurrence hcomplete (by
      intro s h
      have hnext := hguard s h
      dsimp [AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard,
        AoyagiRecurrenceBranchState.toIntroducedState] at hnext
      omega)

end Aoyagi
end DLN
end DLNFibre
