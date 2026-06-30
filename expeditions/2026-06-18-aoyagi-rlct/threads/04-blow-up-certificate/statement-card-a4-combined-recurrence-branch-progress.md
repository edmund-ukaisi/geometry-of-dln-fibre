# Statement card - A4 combined recurrence branch progress

Date: 2026-06-30.

## Statement

Add a recurrence-aware branch progress kernel combining:

- support-growth progress for same-stage `(S,J) -> (S,J+1)` moves;
- stage-budget progress for `(S,J) -> (S+1,0)` handoffs;
- same-domain above-pivot progress for Case 1(1) selected-old lowering.

Lean names:

```text
AoyagiRecurrenceBranchState
AoyagiRecurrenceBranchState.support
AoyagiRecurrenceBranchState.toIntroducedState
AoyagiRecurrenceBranchState.remaining
AoyagiRecurrenceBranchState.stageBudget
AoyagiRecurrenceBranchState.abovePivotCount
AoyagiRecurrenceBranchState.progressStageBase
AoyagiRecurrenceBranchState.progressWeightBase
AoyagiRecurrenceBranchState.progressMeasure
AoyagiRecurrenceBranchState.progressStep
AoyagiRecurrenceBranchState.progressStep_wellFounded
AoyagiRecurrenceBranchState.progressStep_of_toIntroducedState_progress
AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_actualWidth
AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_prefixBound
AoyagiRecurrenceBranchState.case2SuccChild_progress_of_prefixBound
AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_case1DisplayedRowStripPayload
AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_case2DisplayedPayload
AoyagiRecurrenceBranchState.stageSuccZeroWithRecurrence_progress
AoyagiRecurrenceBranchState.sameDomainWithRecurrence_progress_of_abovePivotProgress
AoyagiRecurrenceBranchState.sameDomainWithRecurrence_progress_of_case1SelectedOldLevelMoveData
AoyagiRecurrenceBranchState.case1SelectedOldLevelMove_progress_of_sameDomain
```

The measure is

```text
(remaining * (L+2) + stageBudget) * (#actualWidthLabelFinset + 1)
  + abovePivotCount.
```

The first coordinate handles Case 1(2) and Case 2 support growth.  The second
coordinate handles stage handoff.  The third coordinate handles Case 1(1)
same-domain selected-old lowering.

## Dependencies

- `AoyagiIntroducedLabelBranchState.support_ssubset_case2_increment`
- `AoyagiIntroducedLabelBranchState.progressStep_case1DisplayedRowStrip_jIncrementPayload`
  as the earlier support-growth bridge being generalized to recurrence-aware
  branch states
- `Case2DisplayedJIncrementPayload`
- `IntroducedLabelRecurrenceState.abovePivotLevelProgress_of_case1SelectedOldLevelMoveData`
- `IntroducedLabelRecurrenceState.abovePivotLevelProgress_case1SelectedOldLevelMove_of_sameDomain`
- `introducedLabelFinset_subset_of_state_le`

## Source Reference

Aoyagi PDF p. 16 for Case 1(1) lowering the selected old label from level
`J+J1` to level `J`, and PDF pp. 16-22 for the same-stage `J -> J+1`
continuations and the stage-handoff alternatives in Case 1(2) and Case 2.

## Nonclaims

No source-production payloads, branch guard coverage, terminal branch payloads,
full analytic-atlas branch termination theorem, normal crossings, pole order,
or RLCT is proved.

## Reproduction and Review

Reproduction:

```text
threads/04-blow-up-certificate/reproduction-a4-combined-recurrence-branch-progress.md
```

Review:

```text
threads/04-blow-up-certificate/review-a4-combined-recurrence-branch-progress.md
```
