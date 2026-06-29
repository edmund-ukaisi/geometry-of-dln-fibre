# Reproduction - A2 Case 2 coordinate residual readout

Date: 2026-06-29.

Status: reproduced; Lean target landed; xhigh review passed.

## Scope

This slice exposes the coordinate-level residual readout that was previously
only used internally to prove the selected-entry residual square-sum theorem.

The downstream selected-entry original-loss handoff can consume a hypothesis of
the form

```text
forall y c,
  fixedBaseResidualCoordinate(sourceChart y,c)
    = selectedEntryCenterCoordinate(y,residualCoordEquiv c).
```

The existing Case 2 endpoint-transport theorem supplied only the square-sum
consequence.  The new theorem proves the coordinate readout for the constructed
retained-passive Case 2 source chart.

It does not prove the original-loss socket with
`sourceChart = SelectedEntrySignedBox.CenterCoord.chartMap pivotNext` as the
ambient source point.  That would require additional compatibility: the
selected-entry chart map is not idempotent in general, because applying it twice
multiplies nonpivot coordinates by the pivot coordinate twice.

## Pen-And-Paper Calculation

Let

```text
E(y) = paperEndpointFixedBaseEdgeMatrixOfReverseEdges(sourceChart y).
```

The retained-passive local-source algebra gives the fixed-base residual
coordinate map as the scalar readout of the source-readback residual-factor
product:

```text
fixedBaseResidualCoordinate(sourceChart y)
  = value(residualFactorProduct(sourceReadback(E(y)).C)).
```

Assume the supplied residual-factor matrix handoff:

```text
residualFactorProduct(sourceReadback(E(y)).C)
  = matrix (fun c => selectedEntryCenterChartMap y (residualCoordEquiv c)).
```

Apply scalar readout to both sides.  The elementary identity

```text
value(matrix coord) = coord
```

then gives, coordinate by coordinate,

```text
fixedBaseResidualCoordinate(sourceChart y,c)
  = selectedEntryCenterChartMap y (residualCoordEquiv c).
```

For Case 2, the existing endpoint-transport handoff supplies the matrix identity
above with:

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2),
sourceChart yNext =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0
    ((case2PostPivotSelectedEntryRetainedPassiveData ... yNext eNext).endpointTransport e),
residualCoordEquiv =
  case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext).
```

Composing these two facts gives the Case 2 coordinate readout.

## Lean Landing

The generic bridge is in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_sourceReadback_residualFactorProduct_eq_matrix
```

The Case 2 specialization is in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean`:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

It uses:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
AoyagiResidualBlockCoordinateIndex.value_matrix
```

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

## Boundary Checks

- This proves only coordinate-level residual readout for the constructed
  retained-passive Case 2 source chart.
- It does not prove selected-entry chart image equality or source-rank
  coverage.
- It does not identify an external or original source prior.
- It does not add a determinant-chart pushforward theorem, Jacobian comparison,
  analytic atlas, normal crossings, pole order, or RLCT extraction.
- It does not remove the local source/image equality hypothesis from the
  original-loss selected-entry handoff.
- It does not prove the `SelectedEntryOriginalLossLocalMeasure` socket with
  `CedgeBase (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)` unless a
  separate compatibility theorem identifies that ambient point with the
  constructed retained-passive Case 2 source chart.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** The source-readback residual-factor matrix
identity implies coordinate-level selected-entry residual readout, and the
endpoint-transported Case 2 retained-passive chart satisfies that readout.

**Assumed.** Endpoint equivalences `eNext` and `e`, Case 2 continuation
inequalities `hcont` and `hnext`, and the existing retained-passive
endpoint-transport residual-factor matrix handoff.

**Cited.** None.

**Deferred.** Source/image equality, source-rank coverage, original
source-prior transport, Jacobian comparison, normal crossings, pole order, and
RLCT extraction.
