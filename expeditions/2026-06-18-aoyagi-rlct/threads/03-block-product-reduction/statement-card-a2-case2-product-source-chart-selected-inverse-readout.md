# Statement Card - A2 Case 2 product source chart selected inverse readout

## Claim

For the concrete Case 2 full p.13 product source chart, the selected residual
inverse readout agrees with the selected residual inverse readout of the
underlying passive-theta source chart.

Public Lean name:

```text
case2PassiveThetaEndpointProductSourceChart_inverseReadout_eq_sourceChart
```

## Inputs Used

- the concrete passive-theta endpoint source chart;
- the generic source-dependent p.13 product-coordinate edge-family constructor;
- the unit determinant condition for `ctopMatrix u`;
- the product-coordinate residual readout theorem;
- the pointwise congruence theorem for the fixed-base residual-coordinate map;
- the definition of `case2PassiveThetaEndpointInverseReadout`.

## Output

For

```text
productSourceChart(theta,u)
```

Lean proves:

```text
case2PassiveThetaEndpointInverseReadout
  (productSourceChart(theta,u))
=
case2PassiveThetaEndpointInverseReadout
  (sourceChart theta)
```

## Proof Shape

The selected inverse readout is `preimageOfPivotNeZero` applied to fixed-base
residual block coordinates.  The existing product-chart readout gives equality
of those residual coordinates between the product source chart and the base
source chart.  The two uses of the identity edge-family chart are related to
the product and base source charts by

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point.
```

## Nonclaims

This is not a full product-chart inverse theorem and not passive-theta
recovery.  It does not identify the retained passive fields read by
`sourceReadback`, prove source-image coverage, original/source-prior
transport, Haar transport, a Jacobian formula, normal crossings, pole order,
or RLCT extraction.
