# A2 selected-entry one-chart analytic predicate data

## Scope

This note records the bookkeeping step from the one-chart selected-entry data
records to the forgetful predicate interface in
`SelectedEntryAnalyticAtlasProducer`.

The input records are:

```text
selectedEntryOneChartAnalyticAtlasContext
selectedEntryOneChartAnalyticChartRegularData
selectedEntryOneChartAnalyticTransitionRegularData
selectedEntryOneChartAnalyticUnitRegularData
selectedEntryOneChartAnalyticJacobianVolumeData
```

The target predicates are:

```text
SelectedEntryAnalyticChartRegular
SelectedEntryAnalyticTransitionRegular
SelectedEntryAnalyticUnitRegular
SelectedEntryAnalyticJacobianVolumeCompatible
```

This is a one-chart predicate wrapper only.  It is not source coverage, not a
full `SelectedEntrySuppliedAnalyticAtlasProducer`, not source production, and
not branch termination.

## Predicate Reproduction

Each forgetful predicate has the same shape:

```text
exists ctx, Nonempty (corresponding data ctx).
```

For the fixed selected-entry pivot, the context is:

```text
ctx = selectedEntryOneChartAnalyticAtlasContext pivot.
```

The chart, transition, and unit predicates are inhabited by:

```text
<ctx, <selectedEntryOneChartAnalyticChartRegularData pivot>>
<ctx, <selectedEntryOneChartAnalyticTransitionRegularData pivot>>
<ctx, <selectedEntryOneChartAnalyticUnitRegularData pivot>>
```

For positive signed-box radii `hR : forall i, 0 < R i`, the
Jacobian/volume-compatibility predicate is inhabited by:

```text
<ctx, <selectedEntryOneChartAnalyticJacobianVolumeData pivot hR>>
```

The positive-radius hypothesis is inherited from the Jacobian/volume data
record, where it is used for target nonemptiness and nonzero restricted source
measure.  It is not needed for the chart, transition, or unit predicates.

## No New Calculation

No new Aoyagi calculation is performed here.  The finite selected-entry
calculation remains the already reproduced chart map

```text
(u, r) |-> (x_p = u, x_i = u r_i)
```

with loss unit `1 + sum r_i^2`, Jacobian/prior unit `1`, and Jacobian density
`|u|^(# non-pivot coordinates)`.

This wrapper only exposes those previously verified records through the
existing predicate API.

## Kill Conditions

- Kill if this is described as source-domain coverage.
- Kill if this is described as a full analytic atlas producer.
- Kill if this is used to claim source production or branch termination.
- Kill if this is used as source-prior transport, determinant-chart Haar
  transport, or source-rank coverage.
- Kill if this is used to claim normal-crossing extraction, pole order, or
  RLCT.
