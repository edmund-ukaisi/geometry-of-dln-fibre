# Reproduction - A2 Case 2 with-following active selected-entry reference COV

Date: 2026-07-02.

Status: elementary source-coordinate change-of-variables reproduced and
formalised.  This note does not claim endpoint Haar transport, raw-map
pushforward, source-image coverage, normal crossings, pole order, or RLCT
extraction.

## Source Boundary

Aoyagi's Case 2 calculation, PDF pp. 19-21, uses one selected pivot in the
current residual block.  In the Lean coordinate model this selected-entry
change is the center-coordinate chart

```text
yNext |-> SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext.
```

The already-formalised one-chart Jacobian identity says that the source-side
weighted signed-box measure

```text
(prod_i Lebesgue|(-R_i,R_i)).withDensity
  (fun y => ofReal (sourceDensity pivotNext y))
```

pushes forward under this chart to Lebesgue measure restricted to the chart
image

```text
volume.restrict (chartMap pivotNext '' signedBoxSet R).
```

The enlarged with-following source has product coordinates

```text
Case2PassiveThetaWithFollowingFactor n S J =
  (passiveFields x yNext) x followingFactor.
```

The active selected-entry chart at this source-reference level is therefore

```text
((passive, yNext), F) |-> ((passive, chartMap pivotNext yNext), F).
```

## Calculation

Let

```text
mu_y =
  (prod_i Lebesgue|(-R_i,R_i)).withDensity
    (fun y => ofReal (sourceDensity pivotNext y)).
```

Let `nu` be any s-finite side measure.  Since `id` pushes `nu` to `nu`,
Mathlib's product map theorem gives

```text
map (chartMap x id) (mu_y.prod nu)
  = (map chartMap mu_y).prod (map id nu)
  = (volume.restrict (chartMap '' signedBoxSet R)).prod nu.
```

The passive-left version is the same calculation with factors reversed:

```text
map (id x chartMap) (nu.prod mu_y)
  = nu.prod (volume.restrict (chartMap '' signedBoxSet R)).
```

For the enlarged Aoyagi reference source, first apply the passive-left version
to

```text
case2PassiveThetaReferenceSourceMeasure
  = passiveRef.prod mu_y,
```

and then apply the product-map theorem once more with identity on the
following-factor reference measure.

## Formal Boundary

This result is a source-coordinate reference-measure COV.  It only moves the
selected-entry `yNext` factor and leaves the passive fields and following
factor unchanged.

It does not identify the endpoint topology-tuple image with determinant-chart
Haar measure.  It does not prove a raw-map pushforward or include the
raw-order determinant factor
`retainedPassiveFormalRawOrderJacobianProductAbsDetAt`.  That raw-order factor
enters only after composing the endpoint map with
`topologyTupleEdgeRawOrder`.

