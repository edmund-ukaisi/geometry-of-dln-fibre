# Statement card - A4 Case 2 active guards for source-production totality

Status: Lean implemented after pen-and-paper reproduction.

Reproduction:
`reproduction-a4-case2-active-guard-source-production-totality.md`.

Review:
`review-a4-case2-active-guard-source-production-totality.md`.

## Target

Define active-refined displayed Case 2 branch guards for source production,
prove they cover the active region, and package the existing displayed Case 2
frontier payloads as finite all-pivot source-data records below the analytic
producer payloads.

## Lean Surface

Add a small guard module with:

```text
AoyagiIntroducedLabelBranchState.case2DisplayedActiveContinuingGuard
AoyagiIntroducedLabelBranchState.case2DisplayedActiveActualWidthStoppedGuard
AoyagiIntroducedLabelBranchState.case2DisplayedActiveRowExhaustedStoppedGuard
AoyagiIntroducedLabelBranchState.case2Displayed_activeFrontier_guards_complete

AoyagiRecurrenceBranchState.case2DisplayedActiveContinuingGuard
AoyagiRecurrenceBranchState.case2DisplayedActiveActualWidthStoppedGuard
AoyagiRecurrenceBranchState.case2DisplayedActiveRowExhaustedStoppedGuard
AoyagiRecurrenceBranchState.case2Displayed_activeFrontier_guards_complete
AoyagiRecurrenceBranchState.sameStageChildWithRecurrence_progress_of_activeContinuingGuard

case2AllPivotContinuingGuard
case2AllPivotActualWidthStoppedGuard
case2AllPivotRowExhaustedStoppedGuard
case2AllPivotRowExhaustedSourceSuffixGuard
case2AllPivotRowExhaustedTerminalLastGuard
case2AllPivotGuards_complete
case2AllPivotRowExhaustedStoppedGuard_of_sourceSuffixGuard
case2AllPivotRowExhaustedStoppedGuard_of_terminalLastGuard

Case2AllPivotDisplayedSourceInput
Case2AllPivotDisplayedSourceInput.pivotValue
Case2AllPivotDisplayedSourceInput.continuingRecurrence
Case2AllPivotDisplayedSourceInput.actualWidthRelabelRecurrence

Case2AllPivotContinuingProducedSourceData
Case2AllPivotContinuingProducedSourceData.of_sourceInput
Case2AllPivotContinuingProducedSourceData.child_progress
Case2AllPivotActualWidthStoppedProducedSourceData
Case2AllPivotActualWidthStoppedProducedSourceData.of_sourceInput
Case2AllPivotRowExhaustedTerminalLastProducedSourceData
Case2AllPivotRowExhaustedTerminalLastProducedSourceData.of_sourceInput
Case2AllPivotRowExhaustedStoppedProducedSourceData
Case2AllPivotRowExhaustedStoppedProducedSourceData.of_sourceInput
```

## Source Boundary

Aoyagi pp. 19-22 support the displayed Case 2 pivot chart only when the pivot
entry is present.  The active guard is therefore part of the source-production
domain.  The existing bare stopped equalities remain useful frontier
alternatives after the active guard is assumed; they should not be used as
total payload domains by themselves.

The finite source-data records use already-formalized displayed Case 2
frontier payloads.  They do not supply the analytic chart token, produced
point, chart-domain witness, source-domain witness, or fixed-center alignment
required by `SelectedEntryProducedBranchPayload`.

The row-exhausted source-suffix record is total only over the suffix-refined
guard, which includes `S + 1 <= L`.  It is not data for every bare
row-exhausted stopped state.  The terminal-last row-exhausted record is total
only over the no-suffix guard `S + 1 = L`.

The recurrence data is valued in the displayed coefficient ring `R`.  A final
generic `AoyagiRecurrenceBranchState L n alpha` producer must specialize
`alpha` to that value type, eventually `ℝ`, or add an explicit transport from
displayed pivot values into `alpha`.

## Nonclaims

No `SelectedEntryAtlasProducedBranchData`, `SelectedEntryProducedBranchPayload`,
analytic atlas, source-domain membership, transition regularity,
Jacobian/volume compatibility, generic-`alpha` transport, complete semantic
row-domain coverage, normal crossing, pole order, or RLCT extraction is proved
by this card.
