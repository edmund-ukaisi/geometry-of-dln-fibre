# Statement card - A4 displayed Case 2 branch progress

Date: 2026-06-30.

## Statement

For an introduced-label branch state `(S,J)`, name the displayed Case 2
frontier guards and continuing child `(S,J+1)`.  Under displayed pivot
validity, the three guards are complete; under the continuing guard, the
continuing child is a progress step for the introduced-label measure.

Lean targets:

```text
AoyagiIntroducedLabelBranchState.case2SameStageChild
AoyagiIntroducedLabelBranchState.case2DisplayedContinuingGuard
AoyagiIntroducedLabelBranchState.case2DisplayedActualWidthStoppedGuard
AoyagiIntroducedLabelBranchState.case2DisplayedRowExhaustedStoppedGuard
AoyagiIntroducedLabelBranchState.case2Displayed_frontier_guards_complete
AoyagiIntroducedLabelBranchState.case2SameStageChild_progress_of_prefixBound
AoyagiIntroducedLabelBranchState.case2SameStageChild_progress_of_continuingGuard
```

## Source Reference

Aoyagi PDF pp. 19-22 for the displayed Case 2 continuation and stopped-branch
split.  The finite guard interface and progress relation are expedition
bookkeeping.

## Dependencies

- `Case2DisplayedStepBranch`
- `case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont`
- `AoyagiIntroducedLabelBranchState.progressStep_case2_increment_of_prefixBound`

## Assumptions Kept Explicit

- finite layer bound `L`;
- width function `n`;
- branch-state bounds `1 <= S`, `S <= L`;
- displayed pivot-validity bound `J+1 <= prefixMinNat n (S+1)`;
- continuing guard `J+2 <= prefixMinNat n (S+1)` when producing a continuing
  child progress step.

## Nonclaims

This does not construct branch payloads, prove that source-production data
realizes the child state, make stopped guards exclusive, fill
`SelectedEntryBranchTerminationData`, construct an analytic atlas producer,
extract normal crossings, compute pole order, or extract an RLCT.

## Reproduction and Review

Reproduction:

```text
threads/04-blow-up-certificate/reproduction-a4-case2-displayed-branch-progress.md
```

Review:

```text
threads/04-blow-up-certificate/review-a4-case2-displayed-branch-progress.md
```
