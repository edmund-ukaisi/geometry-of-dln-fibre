# Reproduction - A2 Case 2 produced local-source point readout

Date: 2026-06-29.

Status: reproduced; Lean checked; xhigh review passed.

## Scope

This slice packages an explicit source point for the endpoint-transported
Case 2 selected-entry chart.  Given a nonzero selected-entry residual value,
we choose the fixed-pivot selected-entry inverse coordinates, feed them through
the already constructed retained-passive Case 2 source edge-family map, and
record both local-source membership and exact residual-coordinate readout.

This is independent of the quiver paper and uses only Aoyagi's p.13
retained-passive source chart together with the Case 2 selected-entry chart
calculation.

## Pen-And-Paper Calculation

Let

```text
center = case2ResidualBlockPivotEntries n S (J+1),
p      = (J+2,J+2) in center.
```

For a target center value

```text
value : center -> R
```

with `value p != 0`, define the fixed-pivot selected-entry inverse

```text
y_p = value p,
y_i = value i / value p  for i != p.
```

Then the selected-entry chart recovers the target value:

```text
chartMap p y = value.
```

The already constructed Case 2 retained-passive source family sends these
coordinates to

```text
sourceChart y =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData y).
```

The existing support/readout bridge gives, for every `y`,

```text
sourceChart y in retainedPassiveP13LocalSource,
sourceReadback(sourceChart y).residualFactorProduct
  = matrix(chartMap p y).
```

The residual-coordinate readout bridge then gives

```text
residualBlockCoordinateMap(sourceChart y) c
  = chartMap p y (residualCoordEquiv c).
```

Substituting `chartMap p y = value` yields

```text
residualBlockCoordinateMap(sourceChart y) c
  = value (residualCoordEquiv c).
```

Since `y_p = value p`, the produced coordinates remain in the nonzero-pivot
chart locus.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** A nonzero selected-entry residual target has
an explicit endpoint-transported Case 2 retained-passive local-source point
whose residual-coordinate map is exactly that target value.

**Assumed.** The usual finite Case 2 hypotheses `hS`, `hcont`, `hnext`, a
fixed total-kernel complement, and endpoint transport equivalences.

**Cited.** None.

**Deferred.** Source-rank-stratum membership of the produced source point,
selected-entry source-rank coverage, source-prior transport, Jacobian
comparison, analytic atlas construction, normal crossings, pole order, and
RLCT extraction.

## Lean Outcome

Implemented in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`:

```text
exists_case2EndpointTransport_sourceEdgeFamilyOfData_mem_localSource_and_residualBlockCoordinateMap_eq_value_of_pivot_ne_zero
```

Focused build passed for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`.  Independent
xhigh review passed in
`review-a2-case2-produced-local-source-point-readout.md`.
