# Statement card - A4 Case 2 all-pivot continuing payload progress projection

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducedPayloads.lean
```

Names:

```text
case2AllPivotContinuingPayload_sourceData
case2AllPivotContinuingProducedBranchPayload_child_progress
```

## Claim

The current-center all-pivot continuing produced payload exposes the finite
continuing source-data package used to construct it.  Its produced source data
also supplies the same-stage child recurrence and proves that this child is a
progress step from the parent branch state.

## Inputs

- a recurrence branch state `s : AoyagiRecurrenceBranchState L n Real`;
- displayed Case 2 source input `input`;
- following-factor source rows `Cfollowing`;
- continuing guard `hguard : case2AllPivotContinuingGuard s`;
- a chart equivalence for the current residual-block center.

## Output

The source-data projection is:

```text
(case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput
  input Cfollowing hguard chartEquiv).sourceData =
  Case2AllPivotContinuingProducedSourceData input Cfollowing
```

The progress projection is:

```text
AoyagiRecurrenceBranchState.progressStep L n Real
  (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence s
    payload.producedSourceData.childRecurrence)
  s
```

where `payload` is the same current-center continuing produced payload.

## Dependencies

- Aoyagi Case 2 continuing update on PDF pp. 19-22;
- `Case2AllPivotContinuingProducedSourceData.of_sourceInput`;
- `Case2AllPivotContinuingProducedSourceData.child_progress`.

## Nonclaims

No fixed-context producer, no recurrence-wide source-production field, no
fixed-center transport, no row-exhausted totalization, no analytic atlas
coverage or overlap theorem, no Jacobian/volume compatibility, no normal
crossings, no pole order, and no RLCT extraction.
