# Statement Card - A2 Case 2 product source chart regular/residual readout

## Claim

For the concrete Case 2 passive-theta endpoint source chart, the full p.13
product-coordinate source chart has regular-coordinate readout equal to the
supplied Euclidean vector `u`, and residual-coordinate readout equal to the
residual readout of the underlying passive-theta source chart at `theta`.

Public Lean name:

```text
case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
```

## Inputs Used

- the concrete passive-theta endpoint source chart;
- the generic source-dependent p.13 product-coordinate edge-family constructor;
- the unit determinant condition for `ctopMatrix u`;
- the generic product-coordinate readout theorem specialized at `M := 0`.

## Output

For

```text
productSourceChart(theta,u)
```

Lean proves:

```text
paperEndpointFixedBaseRegularBlockCoordinateMap productSourceChart (theta,u)
  = fun c => u c

paperEndpointFixedBaseResidualBlockCoordinateMap productSourceChart (theta,u)
  =
paperEndpointFixedBaseResidualBlockCoordinateMap sourceChart theta
```

## Proof Shape

Apply

```text
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
```

with `M := 0`, `V := W2`, `Bv := B2`, and
`CedgeBase := case2PassiveThetaEndpointSourceChart ...`.

## Nonclaims

This is not a full product-chart inverse theorem.  It does not prove
source-image coverage, original/source-prior transport, Haar transport, normal
crossings, pole order, or RLCT extraction.
