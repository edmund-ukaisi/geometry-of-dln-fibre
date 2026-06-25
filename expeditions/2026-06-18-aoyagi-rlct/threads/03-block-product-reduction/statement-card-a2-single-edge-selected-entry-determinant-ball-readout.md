# Statement Card - A2 single-edge selected-entry determinant-ball readout

## Claim

For the one-edge selected-entry p.13 product-coordinate family, the determinant
condition on `Ctop(u)` can be discharged uniformly on a sufficiently small
regular-coordinate ball around `0`.  Given `0<Rmax`, there is
`0<R<=Rmax` such that every `u in ball(0,R)` has:

```text
regular readout = u,
residual coordinate c = chartMap pivot y (residualCoordEquiv c),
aoyagiCoordinateSquareSum(residual readout)
  = SelectedEntrySignedBox.CenterCoord.residual pivot y.
```

The same radius works for every selected-entry parameter `y`.

## Lean Statement

```text
exists_pos_radius_le_forall_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEuclidean_readout
```

## Dependencies

- `AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean`
- `paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean`
- `paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean`
- `aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean`

## Kill Conditions

- The radius is only a neighborhood of the centered regular coordinate.  It
  must not be read as a global determinant-chart theorem.
- The theorem remains one-edge.  It does not weaken the multi-edge
  intermediate-factor obstruction.
- The residual-coordinate equivalence remains supplied data.
- The theorem does not identify the first parameter `y` with a source point;
  this is still source-neutral product-coordinate algebra.

## Boundary

This is a determinant-neighborhood wrapper for finite one-edge readout.  It
does not construct source charts, prove source coverage, identify source
measures, prove a local lower bound, produce normal crossings, compute pole
order, or extract RLCT.

## Verification

Focused `SelectedEntryOriginalLossLocalMeasure` build passed.  Full `DLNFibre`
build via local `LAKE_SHARED=.lake-local-shared`, forbidden-marker scan, and
diff check also passed.
