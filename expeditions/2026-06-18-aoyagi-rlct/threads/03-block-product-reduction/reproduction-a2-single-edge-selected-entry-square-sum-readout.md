# Reproduction - A2 single-edge selected-entry square-sum readout

Date: 2026-06-25.

Status: pen-and-paper reproduction before Lean.  This is a finite
postcomposition of the one-edge selected-entry coordinate readout.

## Source Boundary

Aoyagi's p.13 product-coordinate calculation separates regular variables from
the endpoint residual block.  The previous one-edge selected-entry slice showed
that, after supplying a residual-coordinate equivalence

```text
residualCoordEquiv :
  AoyagiResidualBlockCoordinateIndex mu nu ~= center,
```

the one-edge selected-entry product-coordinate family reads out residual
coordinate `c` as

```text
SelectedEntrySignedBox.CenterCoord.chartMap pivot y
  (residualCoordEquiv c).
```

This note records only the scalar square-sum consequence.  It does not add a
source chart, a source-image theorem, or any measure transport.

## Calculation

Let

```text
F(y,u)(c) =
  paperEndpointFixedBaseResidualBlockCoordinateMap
    V Bv U0 hU0 CedgeProd (y,u) c.
```

Under the determinant-unit condition on the regular top block, the one-edge
readout gives

```text
F(y,u)(c) =
  chartMap pivot y (residualCoordEquiv c).
```

The Aoyagi coordinate square-sum is the finite sum of squares of all residual
coordinates.  Therefore

```text
aoyagiCoordinateSquareSum (F(y,u))
  = sum_c (chartMap pivot y (residualCoordEquiv c))^2
  = sum_i (chartMap pivot y i)^2
  = aoyagiCoordinateSquareSum (chartMap pivot y).
```

The middle equality is finite reindexing by `residualCoordEquiv`.  The
selected-entry chart identity then gives

```text
aoyagiCoordinateSquareSum (chartMap pivot y)
  = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

So the one-edge selected-entry product-coordinate family satisfies the scalar
residual equality expected by later signed-box local-measure sockets:

```text
aoyagiCoordinateSquareSum (F(y,u))
  = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

## Lean Target

Add in `SelectedEntryOriginalLossLocalMeasure.lean`:

```text
aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
```

The proof should call the existing one-edge coordinate readout theorem and
then apply
`SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_eq_residual_of_coord_readout`.

## Boundary

- One-edge only.
- Source-neutral finite square-sum readout only.
- The determinant-unit hypothesis on `Ctop(u)` remains explicit.
- The residual-coordinate equivalence is supplied data.
- No source coverage, source-stratum equality, source-measure transport,
  normal crossings, pole order, or RLCT is proved.
