# Reproduction - A2 Case 2 baseJ raw-image inverse-readback density

Date: 2026-07-01.

Status: pen-and-paper reproduction before Lean implementation.

## Question

Can the explicit a.e. factorization hypothesis in the raw-image handoff be
discharged by choosing a concrete raw-side density?

## Calculation

On the local Case 2 determinant/pivot sector, write

```text
Y z =
  case2PassiveThetaEndpointTopologyTuple z

rawMap z =
  topologyTupleEdgeRawOrder (Y z)

jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))

baseJ =
  passiveSource.withDensity jacobianDensity.
```

The local sector theorem supplies

```text
Y z in topologyTupleDetChartSet
```

for every `z in V`.  On this determinant chart, the raw-order readback is a
left inverse:

```text
topologyTupleEdgeRawOrderInverse
  (topologyTupleEdgeRawOrder (Y z))
=
Y z.
```

Define the raw-side density by reading the same source-side Jacobian through
that raw-order inverse:

```text
rawDensity y =
  ofReal
    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
      (topologyTupleEdgeRawOrderInverse y)).
```

Then on `V`,

```text
rawDensity (rawMap z)
=
ofReal
  (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
    (topologyTupleEdgeRawOrderInverse
      (topologyTupleEdgeRawOrder (Y z))))
=
ofReal
  (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))
=
jacobianDensity z.
```

The raw image measure

```text
Measure.map rawMap (passiveSource.restrict V)
```

is supported on the raw-order source-recursive determinant chart because
`rawMap` maps the determinant chart into that raw chart.  On that raw chart,
`topologyTupleEdgeRawOrderInverse` is continuous, and
`retainedPassiveFormalRawOrderJacobianProductAbsDetAt` is continuous at the
inverse point.  Hence `rawDensity` is a.e.-measurable for the raw image.

Applying the generic raw-image handoff gives

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (passiveSource.restrict V)).withDensity rawDensity.
```

## Boundary

The density is not the target-side inverse Jacobian density
`|det D raw (raw^{-1} y)|^{-1}`.  It is the source-side Jacobian product read
back through the raw-order inverse.  Therefore the statement still does not
identify the unweighted raw image

```text
Measure.map rawMap (passiveSource.restrict V)
```

with raw Haar restricted to the raw-order source set.  It proves no
determinant-chart Haar transport, raw Haar normalization, source-image
coverage, source-rank coverage, original source-prior transport, normal
crossings, pole order, or RLCT extraction.
