# Statement Card - A2 single-edge selected-entry square-sum readout

## Claim

For the one-edge selected-entry p.13 product-coordinate family, the residual
coordinate readout implies the scalar selected-entry residual identity.  Under
`IsUnit det(Ctop(u))`,

```text
aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap
    V Bv U0 hU0 CedgeProd (y,u))
= SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

## Lean Statement

```text
aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
```

## Dependencies

- `paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean`
- `paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean`
- `aoyagiCoordinateSquareSum_comp_equiv`
- `SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap`

## Kill Conditions

- Removing the determinant-unit hypothesis would exceed the underlying p.13
  coordinate readout theorem.
- Removing `residualCoordEquiv` would overclaim a canonical finite alignment
  between residual coordinates and selected-entry center coordinates.
- Reading this as a source-chart or source-measure theorem would overclaim:
  the first coordinate of the product-coordinate family is already the
  selected-entry parameter `y`.

## Boundary

This is a one-edge finite square-sum readout theorem.  It does not construct
source charts, prove source coverage, identify source measures, produce normal
crossings, compute pole order, or extract RLCT.

## Verification

Focused `SelectedEntryOriginalLossLocalMeasure` build passed.  Full `DLNFibre`
build via local `LAKE_SHARED=.lake-local-shared`, forbidden-marker scan, and
diff check also passed.
