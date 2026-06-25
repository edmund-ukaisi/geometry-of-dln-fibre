# Statement Card - A2 single-edge selected-entry product-coordinate readout

## Claim

The one-edge p.13 product-coordinate family can be specialized by taking its
residual matrix to be the finite selected-entry chart coordinate matrix.  Under
`IsUnit det(Ctop(u))`, the fixed-base coordinate readout at `(y,u)` has regular
part `u` and residual coordinate

```text
SelectedEntrySignedBox.CenterCoord.chartMap pivot y (residualCoordEquiv c).
```

## Lean Statements

```text
paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean
continuousAt_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean
```

## Dependencies

- `paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean`
- `paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeProductCoordinateEuclidean_residualMatrix`
- `continuousAt_paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean`
- `SelectedEntrySignedBox.CenterCoord.chartMap`
- `SelectedEntrySignedBox.CenterCoord.continuous_chartMap`
- `AoyagiResidualBlockCoordinateIndex.matrix`
- `AoyagiResidualBlockCoordinateIndex.value_matrix`

## Kill Conditions

- Removing `residualCoordEquiv` would overclaim a canonical alignment between
  residual-coordinate indices and selected-entry center coordinates.
- Removing the determinant-unit hypothesis would exceed the p.13 readout
  theorem.
- Treating this as source coverage, inverse chart behavior, or multi-edge
  residual production would be an overclaim.

## Boundary

This is a one-edge finite coordinate-readout theorem plus continuity of the
realized edge family.  It does not construct source charts, prove source
coverage, identify source measures, produce normal crossings, compute pole
order, or extract RLCT.

## Verification

Focused `SelectedEntryOriginalLossLocalMeasure` build passed.  Full `DLNFibre`
build via local `LAKE_SHARED=.lake-local-shared`, `scripts/sorries` with zero
forbidden markers, and `git diff --check` also passed.
