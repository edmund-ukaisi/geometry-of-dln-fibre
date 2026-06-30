# Statement card - A2 selected-entry all-pivot producer shell

Date: 2026-06-29.

## Statement

For the all-pivot selected-entry finite chart family, the already proved
analytic fields over the shared universal-domain context assemble into
`SelectedEntrySuppliedAnalyticAtlasProducer` once branch source production and
branch termination are supplied explicitly.

Lean target:

```text
SelectedEntrySignedBox.CenterCoord.selectedEntryAllPivotSuppliedAnalyticAtlasProducer
```

## Source Reference

Aoyagi PDF pp. 15-22 support the selected-entry coordinate calculation
underlying the analytic fields.  The producer shell is expedition interface
bookkeeping, not a new source-production theorem from Aoyagi's text.

## Dependencies

- `selectedEntryAllPivotAnalyticAtlasContext`
- `selectedEntryAllPivotAnalyticSourceCoverageData`
- `selectedEntryAllPivotAnalyticChartRegularData`
- `selectedEntryAllPivotAnalyticUnitRegularData`
- `selectedEntryAllPivotAnalyticTransitionRegularData`
- `selectedEntryAllPivotAnalyticJacobianVolumeData`
- explicit `SelectedEntryAtlasProducedBranchData`
- explicit `SelectedEntryBranchTerminationData`

## Assumptions Kept Explicit

- a nonempty finite center;
- an enumeration `chartEquiv : Fin center.card ≃ center`;
- a positive selected-entry signed-box radius;
- a chosen branch-state type;
- supplied branch source-production data;
- supplied branch termination data.

## Nonclaims

This does not construct source production, prove branch termination, prove
branch guard exhaustiveness, prove transition semantics for branch states,
extract normal crossings, compute pole order, or extract an RLCT.

## Reproduction and Review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-producer-shell.md
```

Review:

```text
threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-producer-shell.md
```
