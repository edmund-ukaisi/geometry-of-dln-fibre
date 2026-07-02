# Reproduction - A4 Case 2 all-pivot continuing payload progress projection

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean implementation.

## Question

For the current-center Case 2 continuing payload, can the produced payload
expose the source-data package and the recurrence progress proof already
carried by that package?

Answer: yes.  This is a projection theorem, not new source production.  The
existing continuing finite source data stores the child recurrence constructed
from Aoyagi's selected-pivot source chart and proves that the corresponding
same-stage child is a progress step.

## Source Calculation

Aoyagi's Case 2 selected-entry calculation on PDF pp. 19-22 chooses the
residual-block pivot `(J+1,J+1)`.  On that chart the pivot entry is the new
exceptional coordinate `u`, and the remaining residual-block coordinates are
divided by `u`.  The continuing subcase is the case where another pivot remains
after this pivot has been consumed:

```text
J + 2 <= prefixMinNat n (S + 1).
```

The elementary state update is therefore same-stage:

```text
(S, J)  ->  (S, J+1).
```

In the Lean source-data layer this is represented by:

```text
input.continuingRecurrence :
  IntroducedLabelRecurrenceState L n s.S (s.J + 1) R
```

and the branch child is:

```text
AoyagiRecurrenceBranchState.sameStageChildWithRecurrence
  s input.continuingRecurrence
```

The existing source-data constructor records that child recurrence
definitionally and proves the progress relation from the continuing guard.

## Payload Projection

The current-center produced payload constructor

```text
case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput
```

builds a `SelectedEntryProducedBranchPayload` whose `sourceData` type is:

```text
Case2AllPivotContinuingProducedSourceData input Cfollowing
```

and whose `producedSourceData` is produced by:

```text
Case2AllPivotContinuingProducedSourceData.of_sourceInput hguard
```

Therefore two projection statements are source-faithful:

1. the payload's `sourceData` field is the continuing source-data type; and
2. the payload's `producedSourceData.childRecurrence` gives a same-stage child
   satisfying `AoyagiRecurrenceBranchState.progressStep`.

No formula from Aoyagi beyond the Case 2 selected-pivot continuing update is
being newly proved here; the finite source-data layer already contains the
calculation.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotProducedPayloads.lean
```

New declarations:

```text
case2AllPivotContinuingPayload_sourceData
case2AllPivotContinuingProducedBranchPayload_child_progress
```

## Reproduction Verdict

The slice is valid because it merely exposes fields of the already-built
continuing current-center payload.  The recurrence progress statement follows
from:

```text
Case2AllPivotContinuingProducedSourceData.child_progress
```

applied to the payload's produced source data.

## Nonclaims

This does not construct `SelectedEntryAtlasProducedBranchData`, remove the
`sourceProduction` field from the all-pivot producer, solve fixed-center
transport, merge row-exhausted stopped payloads, build analytic chart domains
or source coverage, prove analytic overlap regularity, prove Jacobian/volume
compatibility, normal crossings, pole order, or RLCT.
