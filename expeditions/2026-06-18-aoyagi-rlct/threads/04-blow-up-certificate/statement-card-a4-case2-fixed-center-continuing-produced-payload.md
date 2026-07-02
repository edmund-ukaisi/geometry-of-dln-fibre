# Statement card - A4 Case 2 fixed-center continuing produced payload

Date: 2026-07-02.

Status: formalisation-ready narrow slice.

## Lean Target

Add a constructor for the continuing branch:

```text
case2AllPivotContinuingProducedBranchPayload_of_currentCenterSourceInput
```

It should construct

```text
SelectedEntryProducedBranchPayload
  (selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv)
  (AoyagiRecurrenceBranchState L n Real)
```

only in the fixed-center situation

```text
hcenter :=
  case2ResidualBlockPivotEntries_nonempty_of_cont n s.stage_pos hactive

chartEquiv :=
  any supplied equivalence
    Fin (case2ResidualBlockPivotEntries n s.S s.J).card
      ~= (case2ResidualBlockPivotEntries n s.S s.J : Type)
```

This slice is real-valued, matching the existing displayed all-pivot
source-data layer.

## Required Inputs

- `s : AoyagiRecurrenceBranchState L n Real`.
- `input : Case2AllPivotDisplayedSourceInput s t numerator leastValue`.
- `hguard : case2AllPivotContinuingGuard s`.
- following-factor data `C : Nat -> tau -> Real`.
- a chart equivalence for the current residual-block center.

The constructor may extract the active continuation bound from `hguard` rather
than taking it separately.

## Payload Fields

The payload must use:

- `branchState := s`;
- the displayed all-pivot chart index, obtained through the supplied
  `chartEquiv`;
- the displayed source chart point with `input.u` and `input.residual`;
- universal chart-domain and source-domain witnesses;
- `producedParam` definitionally equal to the chart map at the produced point;
- `sourceData := Case2AllPivotContinuingProducedSourceData input C`;
- `producedSourceData :=
  Case2AllPivotContinuingProducedSourceData.of_sourceInput hguard`.

The record only requires `producedParam` to equal the atlas chart map at the
produced point.  Compatibility between that parameter and the finite
`producedSourceData` witness is not a field of
`SelectedEntryProducedBranchPayload`.

## Boundary

This theorem is not the `sourceProduction` field and must not be named as if
it closes all-pivot source production.  It is one payload constructor for one
fixed current residual-block center.  The next payloads are actual-width
stopped and row-exhausted stopped; the next interface problem is center
alignment for a recurrence-wide atlas.

The public constructor should take the chart equivalence as an input.  It
should not expose or depend on the private canonical finite-subtype chart
equivalence internal to the normal-crossing module.

## Checks

Focused direct Lean check for the new module, full local `lake build
DLNFibre`, `lean/scripts/sorries`, and `git diff --check` are required before
banking.
