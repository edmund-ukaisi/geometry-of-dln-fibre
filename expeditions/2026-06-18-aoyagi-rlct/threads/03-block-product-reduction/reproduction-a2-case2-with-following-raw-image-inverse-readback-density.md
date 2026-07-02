# Reproduction - A2 Case 2 with-following raw-image inverse-readback density

Date: 2026-07-02.

Status: pen-and-paper reproduction completed and formalised.  This note does
not claim determinant-chart Haar transport, endpoint Haar transport, raw-order
Haar transport, source-image coverage, a global Radon-Nikodym derivative,
normal crossings, pole order, or RLCT extraction.

## Source Boundary

Aoyagi's Case 2 selected-pivot calculation, PDF pp. 19-21, supplies the
enlarged source coordinates.  The existing local with-following raw-order
bridge gives an open shrink `V` around the determinant-sector,
selected-pivot-nonzero point where:

```text
Y z lies in the determinant chart,
rawMap z lies in the raw-order determinant source set.
```

This is the exact domain needed for the raw-order inverse readback

```text
topologyTupleEdgeRawOrderInverse.
```

## Calculation

For any with-following source-domain measure `sourceMeasure`, define

```text
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))

baseJ = sourceMeasure.withDensity jacobianDensity.
```

Define the raw-side density by evaluating the same retained-passive formal
product after raw-order inverse readback:

```text
rawDensity y =
  ofReal
    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
      (topologyTupleEdgeRawOrderInverse y)).
```

The raw image of `sourceMeasure.restrict V` is supported on the raw-order
determinant source set `T`, because `rawMap z ∈ T` for every `z ∈ V`.  On `T`,
the inverse readback is continuous and lands in the determinant chart; the
formal raw-order product determinant is continuous on that determinant chart.
Thus `rawDensity` is a.e.-measurable for the actual raw-image measure

```text
Measure.map rawMap (sourceMeasure.restrict V).
```

For `z ∈ V`, the determinant-chart inverse identity gives

```text
topologyTupleEdgeRawOrderInverse (rawMap z) = Y z.
```

Therefore

```text
jacobianDensity z = rawDensity (rawMap z)
```

for `sourceMeasure.restrict V`-a.e. `z`.  Applying the generic raw-image
density handoff gives

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (sourceMeasure.restrict V)).withDensity rawDensity.
```

## Checks

- `sourceMeasure` is arbitrary; no product source prior is inserted.
- The density is the formal product determinant after raw-order inverse
  readback.  It is not named or used as the target-side inverse Jacobian
  density.
- The equality is over the actual raw-image measure, not raw Haar.
- xhigh read-only explorer `Confucius the 2nd` confirmed the statement shape,
  proof route, and nonclaim boundary.
