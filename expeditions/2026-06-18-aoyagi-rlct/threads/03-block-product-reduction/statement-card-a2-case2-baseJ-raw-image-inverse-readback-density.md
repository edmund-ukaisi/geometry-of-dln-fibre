# Statement Card - A2 Case 2 baseJ raw-image inverse-readback density

## Claim

On the local Case 2 passive-theta determinant/pivot sector, the globally
Jacobian-weighted passive-product theta reference satisfies an exact raw-image
density identity with the concrete raw-side density obtained by evaluating the
same retained-passive Jacobian product after raw-order inverse readback:

```text
rawDensity y =
  ofReal
    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
      (topologyTupleEdgeRawOrderInverse y)).
```

Then, for a local open `V subset G`,

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (passiveSource.restrict V)).withDensity rawDensity.
```

Here

```text
baseJ = passiveSource.withDensity jacobianDensity.
```

## Inputs Used

- the local Case 2 determinant/pivot sector theorem, giving determinant-chart
  membership for `Y z` and raw-source-recursive chart membership for
  `rawMap z`;
- `topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder` on the
  determinant chart;
- continuity of raw-order inverse on the raw source-recursive determinant
  chart, plus continuity of the retained-passive formal Jacobian product on
  the determinant chart;
- the generic raw-image `withDensity` handoff.

## Output

The theorem removes the explicit factorization hypothesis from the previous
raw-image handoff by proving it for the concrete inverse-readback density.

## Nonclaims

This is still a theorem over the actual raw image
`Measure.map rawMap (passiveSource.restrict V)`.  It does not identify that
measure with raw Haar restricted to the raw-order source-recursive determinant
chart.  It does not prove determinant-chart Haar transport from
`passiveSource`, raw Haar normalization, original source-prior transport,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction.
