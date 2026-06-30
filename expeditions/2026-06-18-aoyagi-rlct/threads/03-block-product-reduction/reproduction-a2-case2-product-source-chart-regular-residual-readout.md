# Reproduction - A2 Case 2 product source chart regular/residual readout

Date: 2026-06-30.

Status: pen-and-paper check for the concrete full p.13 product-coordinate
readout.  This is not an original-prior transport theorem and not a full
inverse theorem.

## Question

For the passive-theta endpoint source chart

```text
sourceChart : Case2PassiveTheta -> EdgeFamily
```

form the p.13 product source chart

```text
productSourceChart(theta,u) =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    W2 B2 U0 hU0 sourceChart (theta,u).
```

Does the existing product-coordinate readout theorem specialize to the concrete
Case 2 endpoint chart?

## Calculation

The generic regular-suspension theorem says that for any base source chart

```text
CedgeBase : alpha -> EdgeFamily
```

and any Euclidean regular vector `u`, if the decoded top block `Ctop(u)` has
unit determinant, then the source-dependent p.13 product family satisfies

```text
regular(productFamily(x,u)) = u
residual(productFamily(x,u)) = residual(CedgeBase x).
```

In Case 2 take

```text
alpha = Case2PassiveTheta
CedgeBase = case2PassiveThetaEndpointSourceChart W2 B2 n hS hcont hnext hU0 eNext e
M = 0
```

so that `Fin (M+3) = Fin 3` and `Fin (M+2) = Fin 2`.  The theorem becomes

```text
regular(productSourceChart(theta,u)) = u
residual(productSourceChart(theta,u)) = residual(sourceChart theta).
```

The only pointwise hypothesis is

```text
IsUnit (det (ctopMatrix u)).
```

This is the exact p.13 block-coordinate calculation: the added regular
variables are read back as themselves, while the reduced residual coordinates
are inherited from the passive-theta source chart.

## Boundary

The theorem does not define a map

```text
EdgeFamily -> Case2PassiveTheta × EuclideanSpace R Coord.
```

The existing library has passive-theta readback for the base chart and
coordinate readout for the product chart, but not a full product-chart inverse.
This readout therefore cannot by itself prove source-image coverage, external
prior support, Haar transport, or a source-prior density identity.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
```

The proof should be only a specialization of

```text
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
```

with `M := 0` and the concrete Case 2 passive-theta endpoint source chart.

## Nonclaims

No full inverse/readback to `(theta,u)`, no source-image coverage, no original
or external source-prior transport, no Haar transport, no normal crossings, no
pole order, and no RLCT extraction.
