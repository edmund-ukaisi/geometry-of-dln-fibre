# Statement card - A4 Case 2 branch-indexed current-center payloads

Date: 2026-07-02.

Status: Lean support-layer target.

Source reproduction:
`reproduction-a4-case2-branch-indexed-current-center-payloads.md`.

## Claim

The fixed-current-center all-pivot Case 2 payload constructors can be packaged
as branch-indexed current-center payload data.  The current center for a branch
state `s` is

```text
case2ResidualBlockPivotEntries n s.S s.J.
```

This branch-indexed package is not a
`SelectedEntryAtlasProducedBranchData`, because that producer record fixes one
atlas context and hence one center for all branch states.

## Lean Target

New module:

```text
DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotBranchIndexedPayloads
```

Definitions:

```text
case2AllPivotCurrentCenter
case2AllPivotFixedCenterAligned
case2ResidualBlockPivotEntries_ne_succ_of_cont
case2AllPivotCurrentCenter_ne_sameStageChildWithRecurrence_of_continuing
case2AllPivot_sameStageChild_active_of_continuing
not_fixedCenterAligned_parent_and_sameStageChild_of_continuing
Case2AllPivotFixedCenterAlignment
Case2AllPivotFixedCenterAlignment.not_alignment_of_continuing
Case2AllPivotCurrentCenterProducedPayload
Case2AllPivotCurrentCenterProducedPayload.of_continuing
Case2AllPivotCurrentCenterProducedPayload.of_actualWidthStopped
Case2AllPivotCurrentCenterProducedPayload.of_rowExhaustedTerminalLast
Case2AllPivotCurrentCenterProducedPayload.of_rowExhaustedSourceSuffix
Case2AllPivotBranchIndexedProducedPayloadData
```

## Proof Plan

Use the existing fixed-current-center constructors:

```text
case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput
case2AllPivotActualWidthStoppedProducedBranchPayload_of_currentCenterSourceInput
case2AllPivotRowExhaustedTerminalLastProducedBranchPayload_of_currentCenterSourceInput
case2AllPivotRowExhaustedSourceSuffixProducedBranchPayload_of_currentCenterSourceInput
```

Wrap each constructor with its public `chartEquiv` and record the literal
payload branch-state law.

Name the fixed-center alignment condition separately:

```text
for every active branch state s,
  center = case2ResidualBlockPivotEntries n s.S s.J.
```

## Kill Conditions

Kill or rescope if the implementation:

- adds a conversion to `SelectedEntryAtlasProducedBranchData`;
- fills source data with `Unit`, `True`, `PUnit`, `Nonempty`, or
  `SourceProductionObligation`;
- merges terminal-last and source-suffix row-exhausted data into one total
  semantic row payload;
- claims fixed-center alignment without an explicit alignment field;
- uses a generic recurrence value type without transport from displayed real
  source values;
- claims transition regularity, Jacobian/volume compatibility, normal
  crossings, pole order, or RLCT extraction.

## Expected Verification

Focused build:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotBranchIndexedPayloads
```

Then direct warning-clean elaboration for the touched Lean file, full
`lake build DLNFibre`, no-sorry audit, `git diff --check`, and forbidden
placeholder-source-data grep.
