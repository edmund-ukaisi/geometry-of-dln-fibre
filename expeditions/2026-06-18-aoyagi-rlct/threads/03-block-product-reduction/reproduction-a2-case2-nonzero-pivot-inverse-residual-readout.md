# Reproduction - A2 Case 2 nonzero-pivot inverse residual readout

Date: 2026-06-29.

Status: reproduced; Lean target landed; xhigh review passed.

## Scope

This slice isolates the honest inverse-chart statement behind the failed
temptation to feed the constructed Case 2 source chart directly through a
second selected-entry `chartMap`.

The selected-entry center chart

```text
chartMap(pivot,y)
```

keeps the pivot coordinate and multiplies every nonpivot coordinate by the
pivot.  Hence it is not idempotent: applying it twice multiplies nonpivot
coordinates by the pivot twice.  The correct bridge from an ambient center
coordinate value `value` back to source coordinates is the existing partial
inverse

```text
preimageOfPivotNeZero(pivot,value),
```

which is valid on the nonzero-pivot locus.

## Pen-And-Paper Calculation

Let `x : center -> R` be a target center-coordinate vector with

```text
x_pivot != 0.
```

The selected-entry inverse is

```text
y_pivot = x_pivot,
y_i = x_i / x_pivot        for i != pivot.
```

Then

```text
chartMap(pivot,y)_pivot = y_pivot = x_pivot,
chartMap(pivot,y)_i = y_pivot * y_i = x_pivot * (x_i / x_pivot) = x_i.
```

Thus

```text
chartMap(pivot, preimageOfPivotNeZero(pivot,x)) = x.
```

The retained-passive source-readback coordinate theorem already gives

```text
fixedBaseResidualCoordinate(sourceChart y,c)
  = chartMap(pivot,y)(residualCoordEquiv c).
```

Substitute

```text
y = preimageOfPivotNeZero(pivot,x).
```

The selected-entry inverse identity gives

```text
fixedBaseResidualCoordinate(sourceChart(preimageOfPivotNeZero(pivot,x)),c)
  = x(residualCoordEquiv c).
```

For the endpoint-transported Case 2 source chart, this says that on the
nonzero selected-pivot locus, the constructed retained-passive Case 2 source
chart pulled back along the selected-entry inverse recovers the ambient center
coordinates as fixed-base residual coordinates.

## Lean Landing

The selected-entry left-inverse lemma is in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`:

```text
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
```

The generic retained-passive inverse readout is in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_sourceReadback_residualFactorProduct_eq_matrix_preimageOfPivotNeZero
```

The Case 2 specialization is in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero
```

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

## Boundary Checks

- This is a punctured-chart algebra bridge on the selected-pivot nonzero locus.
- It does not prove continuity of `preimageOfPivotNeZero` at the exceptional
  divisor.
- It does not prove selected-entry chart image equality, source-rank coverage,
  source-prior transport, determinant-chart pushforward, Jacobian comparison,
  analytic atlas construction, normal crossings, pole order, or RLCT.
- It does not remove the local source/image equality hypothesis from the
  original-loss selected-entry handoff.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** On the selected-pivot nonzero locus, pulling
ambient center coordinates back by `preimageOfPivotNeZero` before applying the
constructed retained-passive Case 2 source chart makes the fixed-base residual
coordinates equal the ambient center coordinates.

**Assumed.** Endpoint equivalences `eNext` and `e`, Case 2 continuation
inequalities `hcont` and `hnext`, and the existing retained-passive
endpoint-transport residual-factor matrix handoff.

**Cited.** None.

**Deferred.** The exceptional divisor, local source/image equality,
source-rank coverage, original source-prior transport, Jacobian comparison,
normal crossings, pole order, and RLCT extraction.
