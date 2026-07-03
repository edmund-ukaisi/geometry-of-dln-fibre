# A2 with-following edge-family product-residual readout

Date: 2026-07-03.

This note records the small bridge needed before composing the
with-following source-side residual integral with an edge-family readback
transfer.

## Objects

For an enlarged Case 2 passive-theta coordinate

```text
z : Case2PassiveThetaWithFollowingFactor (rho := Fin (finrank R U0)) (tau := tau) n S J
```

the source-side product residual used by the finite-integral theorem is

```text
productResidual z ij =
  ((residualFactorProduct
      (case2PassiveThetaWithFollowingFactorEndpointRetainedData
        n hS hcont hnext z eNext e).C
      (Fin.last 2) 0 _).submatrix (e (Fin.last 2)) (e 0)) ij.1 ij.2.
```

For an endpoint edge family `E`, the edge-family readout uses the same formula
after applying the endpoint source-chart readback:

```text
edgeResidual E =
  productResidual
    (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
      W2 B2 n hS hnext hU0 e E).
```

The direct raw source-readback readout is the fixed-base residual-block
coordinate map, reindexed by the endpoint equivalences:

```text
rawEdgeResidual E ij =
  paperEndpointFixedBaseResidualBlockCoordinateMap
    W2 B2 U0 hU0 (fun E => E) E
    (e (Fin.last 2) ij.1, e 0 ij.2).
```

## Calculation

On the local source-chart neighborhood already produced by the source-chart
theorem we have

```text
readback (sourceChart z) = z.
```

Therefore, for every coordinate `ij`,

```text
edgeResidual (sourceChart z) ij
  = productResidual (readback (sourceChart z)) ij
  = productResidual z ij.
```

The square-sum identity follows by function congruence:

```text
aoyagiCoordinateSquareSum (edgeResidual (sourceChart z))
  = aoyagiCoordinateSquareSum (productResidual z).
```

For the raw fixed-base readout, assume the endpoint retained data attached to
`z` is in the determinant chart.  The source-chart definition realizes

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges (sourceChart z)
  = (retainedData z).edgeMatrix.
```

Hence the fixed-base source readback recovers the endpoint retained data:

```text
sourceReadback (paperEndpointFixedBaseEdgeMatrixOfReverseEdges (sourceChart z))
  = retainedData z.
```

The generic residual-block coordinate theorem rewrites
`paperEndpointFixedBaseResidualBlockCoordinateMap` as the residual-factor
product of this `sourceReadback`.  Substituting the preceding equality gives

```text
rawEdgeResidual (sourceChart z) = productResidual z,
```

and therefore the corresponding square-sum identity.

## Boundary

This is only pointwise finite-coordinate algebra.  It proves no new
measurability theorem for the edge-family integrand, no source-side finite
integral, no original-prior transfer, no determinant-Haar transport, no normal
crossing statement, no pole order, and no RLCT statement.
