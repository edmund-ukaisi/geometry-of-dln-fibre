# Statement card - A4 recurrence-aware Case 2 branch progress

Date: 2026-06-30.

## Statement

Add recurrence-aware selected-entry branch-progress adapters for the displayed
Case 2 same-stage continuation.

Lean names:

```text
AoyagiRecurrenceBranchState.case2DisplayedActiveGuard
selectedEntryCase2DisplayedRecurrencePrefixBoundBranchProgressData
selectedEntryCase2DisplayedRecurrenceContinuingBranchProgressData
```

The main adapter consumes:

```text
initialRecurrence : IntroducedLabelRecurrenceState L n 1 0 alpha
sourceProduction :
  SelectedEntryAtlasProducedBranchData ctx
    (AoyagiRecurrenceBranchState L n alpha)
childRecurrence :
  forall s, sourceProduction.continuingGuard s ->
    IntroducedLabelRecurrenceState L n s.S (s.J+1) alpha
hcomplete :
  forall s, AoyagiRecurrenceBranchState.case2DisplayedActiveGuard s ->
    sourceProduction.continuingGuard s or
    sourceProduction.actualWidthStoppedGuard s or
    sourceProduction.rowExhaustedStoppedGuard s
hbound :
  forall s h, s.J+1 <= prefixMinNat n (s.S+1)
```

and returns:

```text
SelectedEntryAtlasBranchProgressData sourceProduction
  (selectedEntryRecurrenceBranchTerminationData
    C L n alpha hL initialRecurrence).
```

## Dependencies

- `SelectedEntryAtlasBranchProgressData`
- `selectedEntryRecurrenceBranchTerminationData`
- `AoyagiRecurrenceBranchState.sameStageChildWithRecurrence`
- `AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_prefixBound`

## Nonclaims

No recurrence data construction, source-production payload, branch-guard
construction, terminal payload, chart construction, analytic atlas field,
normal crossings, pole order, or RLCT is proved.

## Reproduction

```text
threads/04-blow-up-certificate/reproduction-a4-recurrence-case2-branch-progress.md
```

## Review

```text
threads/04-blow-up-certificate/review-a4-recurrence-case2-branch-progress.md
```
