# Reproduction - A4 Case 2 branch-indexed continuing progress projection

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before Lean implementation.

## Question

After the fixed-current-center continuing payload is wrapped as
branch-indexed current-center data, can we still expose the continuing
source-data package and the same-stage child progress proof?

Answer: yes.  The branch-indexed wrapper adds only the chart-equivalence token,
the produced payload, and the definitional state law.  It does not change the
produced payload.  Therefore the existing fixed-current-center source-data and
child-progress projections transport through the wrapper by definitional
reduction.

## Source Calculation

Aoyagi's Case 2 continuing update on PDF pp. 19-22 is the same update used by
the fixed-current-center payload:

```text
(S, J) -> (S, J+1).
```

The continuing guard records that a next pivot remains:

```text
J + 2 <= prefixMinNat n (S + 1).
```

The finite source-data record already stores the child recurrence

```text
childRecurrence : IntroducedLabelRecurrenceState L n s.S (s.J + 1) Real
```

and proves

```text
AoyagiRecurrenceBranchState.progressStep L n Real
  (AoyagiRecurrenceBranchState.sameStageChildWithRecurrence s childRecurrence)
  s.
```

The branch-indexed constructor is:

```text
Case2AllPivotCurrentCenterProducedPayload.of_continuing
  input Cfollowing hguard chartEquiv
```

and its `payload` field is definitionally:

```text
case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput
  input Cfollowing hguard chartEquiv.
```

Thus the source-data field and progress proof are the same ones already
checked for the fixed-current-center payload.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotBranchIndexedPayloads.lean
```

New declarations:

```text
Case2AllPivotCurrentCenterProducedPayload.of_continuing_payload_sourceData
Case2AllPivotCurrentCenterProducedPayload.of_continuing_payload_child_progress
```

## Reproduction Verdict

The slice is valid because it is a projection through an existing wrapper.  It
does not introduce new Aoyagi source algebra.  The only mathematical content is
the already-reproduced continuing same-stage `J -> J+1` update and the
previously proved source-data progress theorem.

## Nonclaims

No `SelectedEntryAtlasProducedBranchData`, no recurrence-wide fixed-center
transport, no conversion from branch-indexed payloads to the fixed all-pivot
producer, no row-exhausted totalization, no source coverage, no transition or
volume compatibility, no normal crossings, no pole order, and no RLCT
extraction is proved here.
