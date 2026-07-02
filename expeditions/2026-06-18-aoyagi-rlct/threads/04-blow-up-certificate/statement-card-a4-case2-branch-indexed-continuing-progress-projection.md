# Statement card - A4 Case 2 branch-indexed continuing progress projection

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotBranchIndexedPayloads.lean
```

Names:

```text
Case2AllPivotCurrentCenterProducedPayload.of_continuing_payload_sourceData
Case2AllPivotCurrentCenterProducedPayload.of_continuing_payload_child_progress
```

## Claim

The branch-indexed current-center wrapper for the all-pivot Case 2 continuing
payload exposes the same finite continuing source-data package and same-stage
child progress proof as the fixed-current-center payload it wraps.

## Inputs

- a recurrence branch state `s : AoyagiRecurrenceBranchState L n Real`;
- displayed Case 2 source input `input`;
- following-factor source rows `Cfollowing`;
- continuing guard `hguard : case2AllPivotContinuingGuard s`;
- a chart equivalence for the current residual-block center.

## Output

The source-data projection is:

```text
((Case2AllPivotCurrentCenterProducedPayload.of_continuing
  input Cfollowing hguard chartEquiv).payload).sourceData =
  Case2AllPivotContinuingProducedSourceData input Cfollowing
```

The child-progress projection is:

```text
AoyagiRecurrenceBranchState.progressStep L n Real
  (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence s
    (((Case2AllPivotCurrentCenterProducedPayload.of_continuing
      input Cfollowing hguard chartEquiv).payload)
        .producedSourceData).childRecurrence)
  s
```

## Dependencies

- Aoyagi Case 2 continuing update on PDF pp. 19-22;
- `Case2AllPivotCurrentCenterProducedPayload.of_continuing`;
- `case2AllPivotContinuingPayload_sourceData`;
- `case2AllPivotContinuingProducedBranchPayload_child_progress`.

## Nonclaims

No fixed-context producer, no recurrence-wide source-production field, no
fixed-center transport, no row-exhausted totalization, no analytic atlas
coverage or overlap theorem, no Jacobian/volume compatibility, no normal
crossings, no pole order, and no RLCT extraction.
