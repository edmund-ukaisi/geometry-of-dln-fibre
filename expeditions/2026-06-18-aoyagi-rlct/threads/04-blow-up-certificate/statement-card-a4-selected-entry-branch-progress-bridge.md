# Statement card - A4 selected-entry branch progress bridge

Date: 2026-06-30.

## Statement

Add a narrow interface between selected-entry branch source production and
branch termination:

```text
SelectedEntryAtlasBranchProgressData
```

Then instantiate the termination relation for introduced-label progress and
prove the displayed Case 2 continuing-child bridge:

```text
AoyagiIntroducedLabelBranchState.case2DisplayedActiveGuard
selectedEntryIntroducedLabelBranchTerminationData
selectedEntryCase2DisplayedPrefixBoundBranchProgressData
selectedEntryCase2DisplayedContinuingBranchProgressData
```

## Source Reference

Aoyagi PDF pp. 19-22 for the displayed Case 2 same-stage continuation
`(S,J) -> (S,J+1)` and the stopped alternatives.  The branch-child interface
and introduced-label termination relation are expedition bookkeeping.

## Dependencies

- `SelectedEntryAtlasProducedBranchData`
- `SelectedEntryBranchTerminationData`
- `AoyagiIntroducedLabelBranchState.progressStep_wellFounded`
- `AoyagiIntroducedLabelBranchState.case2SameStageChild_progress_of_prefixBound`
- `AoyagiIntroducedLabelBranchState.case2SameStageChild_progress_of_continuingGuard`

## Assumptions Kept Explicit

- `1 <= L` to choose the initial branch state `(1,0)`;
- a supplied `SelectedEntryAtlasProducedBranchData`;
- a proof that the supplied branch guards cover the displayed active guard;
- either a proof that continuing source-production guards imply the displayed
  pivot-validity bound, or a proof that they imply the displayed continuing
  guard.

## Nonclaims

No source-production payload is constructed.  No payload source data is proved
to realize the child state.  No stopped branch is given a fake child.  No
branch guard exclusivity, chart coverage, analytic regularity, normal
crossings, pole order, or RLCT is proved.

## Reproduction and Review

Reproduction:

```text
threads/04-blow-up-certificate/reproduction-a4-selected-entry-branch-progress-bridge.md
```

Review:

```text
threads/04-blow-up-certificate/review-a4-selected-entry-branch-progress-bridge.md
```
