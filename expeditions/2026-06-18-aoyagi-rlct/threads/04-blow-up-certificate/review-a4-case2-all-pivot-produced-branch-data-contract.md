# Review - A4 Case 2 all-pivot produced-branch-data contract

Date: 2026-07-02.

Status: PASS.

## Scope For Review

Reviewed artifacts:

- `construction-card-a4-case2-all-pivot-produced-branch-data-contract.md`;
- `reproduction-a4-case2-all-pivot-produced-branch-data-contract.md`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasProducer.lean`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerShell.lean`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducerTermination.lean`;
- `lean/DLNFibre/DLN/Aoyagi/BlowupBranchProgress.lean`;
- Aoyagi PDF pp. 19-22.

## Controller Pre-Review Checklist

The packet keeps the target as the exact remaining producer field:

```text
SelectedEntryAtlasProducedBranchData
  (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
  (AoyagiRecurrenceBranchState L n alpha)
```

It uses the existing displayed Case 2 guard definitions rather than inventing
new predicates.  The old-state convention is checked: `(S,J)` is pre-pivot,
the selected pivot is `J+1`, and the continuing child is `(S,J+1)` under
`J+2 <= prefixMinNat n (S+1)`.

The packet does not claim that progress data supplies source production.  It
separates:

- guard completeness;
- continuing-child recurrence/progress;
- produced chart point/source parameter;
- branch-specific source data.

The packet rejects the main known overclaims:

- placeholder guards;
- `sourceData := Unit`;
- `SourceProductionObligation` as analytic source production;
- fixed-center recurrence-wide use without alignment;
- merging the two stopped payloads;
- claiming analytic atlas construction, normal crossings, pole order, or RLCT.

## Independent Review Result

Reviewer: xhigh read-only `Huygens`.

Verdict: PASS.  No concrete findings.

The reviewer confirmed that the packet uses the existing displayed Case 2
guards through `s.toIntroducedState`, and that these match the Lean definitions
in `BlowupBranchProgress.lean`.  The old-state convention is correct:
`(S,J)` is pre-pivot, the selected pivot is `J+1`, and the continuing child is
`(S,J+1)` under `J+2 <= prefixMinNat n (S+1)`.

The fixed-center obstruction was also accepted.  The all-pivot producer builds
one fixed `selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv`, while
the natural Aoyagi Case 2 center is indexed by the current `(S,J)`.  A
recurrence-wide theorem therefore needs a fixed-state restriction, explicit
center alignment, or a dependent branch-indexed atlas interface.

The reviewer found no overclaim from Aoyagi pp. 19-22.  The packet limits the
paper support to the selected-pivot chart, `b'_i = u b_i`, regular `Q/P`,
transported `C'`, cleared `D'''`, product identity, and continue/stop prose,
and keeps analytic chart/domain/producer records as missing constructed data.

The payload list and state laws match the current
`SelectedEntryAtlasProducedBranchData` / `SelectedEntryProducedBranchPayload`
interface.  No additional kill condition was requested.
