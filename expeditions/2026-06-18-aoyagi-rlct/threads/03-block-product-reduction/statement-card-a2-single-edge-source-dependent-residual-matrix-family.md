# Statement Card - A2 single-edge source-dependent residual-matrix family

## Claim

For a one-edge fixed-base p.13 product-coordinate family built from a
base-point-dependent residual matrix `Dbase x`, the pointwise coordinate
readout at `(x,u)` has regular part `u` and residual part
`AoyagiResidualBlockCoordinateIndex.value (Dbase x)`, assuming
`IsUnit det(Ctop(u))`.

## Lean Statements

```text
paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeProductCoordinateEuclidean_residualMatrix
continuous_productCoordinateSingleEdgeMatrix
continuousAt_paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean
```

## Dependencies

- `paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean`
- `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_singleEdgeProductCoordinateEuclidean`
- `paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point`
- `paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point`
- fixed-base prescribed-matrix realisation continuity

## Kill Conditions

- Removing the determinant-unit hypothesis invalidates the current p.13
  chart readout proof.
- Reading this as a multi-edge arbitrary-terminal-residual theorem conflicts
  with the formal residual-factor rank obstruction.
- Reading it as source coverage or a selected-entry chart theorem is an
  overclaim.

## Boundary

This is one-edge finite algebra plus continuity under `Continuous Dbase`.  It
does not construct `Dbase`, source coverage, source-measure transport, normal
crossings, pole order, or RLCT.

## Verification

Focused `ChartTopology` and `RegularSuspensionCoordinates` builds passed.  Full
`DLNFibre` build via local `LAKE_SHARED=.lake-local-shared`, `scripts/sorries`
with zero forbidden markers, and `git diff --check` also passed.
