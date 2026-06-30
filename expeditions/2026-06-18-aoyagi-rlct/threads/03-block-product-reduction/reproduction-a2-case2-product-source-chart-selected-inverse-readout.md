# Reproduction - A2 Case 2 product source chart selected inverse readout

Date: 2026-06-30.

Status: pen-and-paper check before Lean for the selected residual inverse
component of the p.13 product source chart.

## Question

The passive-theta readback has a selected-entry residual component

```text
case2PassiveThetaEndpointInverseReadout : EdgeFamily -> Center -> R.
```

Does the full p.13 product source chart preserve this selected residual
readout from the underlying passive-theta source chart?

## Calculation

The selected inverse readout is defined by taking fixed-base residual block
coordinates of the ambient edge family, reindexing them by

```text
case2PassiveThetaEndpointResidualCoordEquiv
```

and applying the fixed-pivot selected-entry inverse

```text
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero.
```

The product-source-chart readout theorem already proves

```text
residual(productSourceChart(theta,u)) = residual(sourceChart theta)
```

under the determinant-chart condition `IsUnit(det(ctopMatrix u))`.  Since the
selected inverse readout uses only these residual coordinates, it follows that

```text
inverseReadout(productSourceChart(theta,u))
  =
inverseReadout(sourceChart theta).
```

## Boundary

This is one component of a possible product-chart readback, not the full
readback.  It does not identify the retained passive fields read by
`sourceReadback`; hence it still does not prove

```text
case2PassiveThetaEndpointSourceChartReadback(productSourceChart(theta,u))
  = theta.
```

Together with the regular readback theorem, this records that the product
chart exposes `u` and preserves the selected residual inverse.  The remaining
missing piece for a full `(theta,u)` inverse is a retained-passive/sourceReadback
identity for the product-coordinate edge family.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
case2PassiveThetaEndpointProductSourceChart_inverseReadout_eq_sourceChart
```

The proof uses:

```text
case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
case2PassiveThetaEndpointInverseReadout
```

## Nonclaims

No full inverse/readback to `(theta,u)`, no passive-theta recovery from the
product chart, no sourceReadback retained-data identity, no source-image
coverage, no original/source-prior transport, no Haar transport, no Jacobian
formula, no normal crossings, no pole order, and no RLCT extraction.
