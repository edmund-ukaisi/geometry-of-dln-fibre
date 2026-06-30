# Statement Card - A2 Case 2 product source chart regular readback

## Claim

For the concrete Case 2 full p.13 product source chart, the source-side
regular-block readback recovers the supplied Euclidean regular variable `u`.

Public Lean names:

```text
case2PassiveThetaEndpointProductSourceChartRegularReadback
case2PassiveThetaEndpointProductSourceChart_regularReadback_eq
```

## Inputs Used

- the concrete passive-theta endpoint source chart;
- the generic source-dependent p.13 product-coordinate edge-family constructor;
- the unit determinant condition for `ctopMatrix u`;
- the existing product-coordinate regular/residual readout theorem;
- the pointwise congruence theorem for the fixed-base regular-coordinate map;
- `EuclideanSpace.equiv Coord R`.

## Output

For

```text
productSourceChart(theta,u)
```

Lean proves:

```text
case2PassiveThetaEndpointProductSourceChartRegularReadback W2 B2 hU0
  (productSourceChart(theta,u)) = u
```

## Proof Shape

The readback views an ambient `EdgeFamily` as a point of the identity
edge-family chart and applies

```text
paperEndpointFixedBaseRegularBlockCoordinateMap
```

then converts `Coord -> R` to `EuclideanSpace R Coord` using
`EuclideanSpace.equiv.symm`.

At `productSourceChart(theta,u)`, pointwise congruence identifies the identity
edge-family readout with the product-family readout.  The already-proved
product-chart readout gives `fun c => u c`, and
`ContinuousLinearEquiv.symm_apply_apply` converts this coordinate function back
to `u`.

## Nonclaims

This is not a full product-chart inverse theorem and not a passive-theta
readback theorem.  It does not recover `theta`, prove source-image coverage,
original/source-prior transport, Haar transport, a Jacobian formula, normal
crossings, pole order, or RLCT extraction.
