# Reproduction - A2 Case 2 product source chart regular readback

Date: 2026-06-30.

Status: pen-and-paper check for the source-side readback of only the p.13
regular Euclidean variables.

## Question

Given an ambient two-edge family `X`, the fixed-base p.13 regular-coordinate
map reads a coordinate function

```text
regular(X) : Coord -> R.
```

Can we package this as a map back to the Euclidean regular-coordinate space,
and does it recover the supplied `u` on the concrete Case 2 product source
chart?

## Calculation

Define the regular readback by viewing the ambient edge-family type as its own
coordinate chart via the identity map, applying the fixed-base
regular-coordinate map at `X`, and then using the linear equivalence

```text
EuclideanSpace R Coord ~= Coord -> R.
```

Thus

```text
regularReadback(X) =
  (EuclideanSpace.equiv Coord R).symm(regular(identityChart, X)).
```

For the product source chart, the identity-chart readout agrees with the
product-family readout at `productSourceChart(theta,u)` because
`paperEndpointFixedBaseRegularBlockCoordinateMap` depends only on the edge
family at the queried point.  The existing product readout theorem gives

```text
regular(productSourceChart(theta,u)) = fun c => u c
```

under the determinant-chart condition `IsUnit(det(ctopMatrix u))`.  Applying
`(EuclideanSpace.equiv Coord R).symm` therefore recovers `u`.

## Boundary

This is deliberately only the regular-coordinate component of a source-side
readback.  It does not recover the passive/base parameter `theta`, and it is
not a full inverse to

```text
(theta,u) -> productSourceChart(theta,u).
```

The passive-theta readback for the base chart cannot simply be reused here,
because the product chart changes the edge family by inserting the p.13
regular variables.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
case2PassiveThetaEndpointProductSourceChartRegularReadback
case2PassiveThetaEndpointProductSourceChart_regularReadback_eq
```

The proof uses:

```text
paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
EuclideanSpace.equiv
```

## Nonclaims

No full inverse/readback to `(theta,u)`, no passive-theta recovery from the
product chart, no source-image coverage, no original/source-prior transport, no
Haar transport, no Jacobian formula, no normal crossings, no pole order, and no
RLCT extraction.
