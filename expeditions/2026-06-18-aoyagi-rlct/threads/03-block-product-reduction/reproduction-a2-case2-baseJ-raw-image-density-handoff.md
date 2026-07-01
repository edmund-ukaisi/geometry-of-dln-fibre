# Reproduction - A2 Case 2 baseJ raw-image density handoff

Date: 2026-07-01.

Status: pen-and-paper reproduction before Lean hardening.

## Question

What exact measure statement follows from the globally Jacobian-weighted
passive-theta reference

```text
baseJ = passiveSource.withDensity jacobianDensity
```

without assuming that the passive-product theta measure transports to raw Haar?

## Calculation

Let `V` be the local determinant/pivot sector returned by the Case 2
passive-theta source-measure theorem.  On this sector, the raw-order map is
continuous, hence a.e.-measurable for `passiveSource.restrict V`.

Suppose `rawDensity` is a.e.-measurable for the raw-image measure

```text
Measure.map rawMap (passiveSource.restrict V)
```

and that the theta-side density factors through `rawMap` almost everywhere:

```text
jacobianDensity z = rawDensity (rawMap z)
```

for `passiveSource.restrict V`-a.e. `z`.

Restricting a weighted measure to `V` gives

```text
(passiveSource.withDensity jacobianDensity).restrict V
=
(passiveSource.restrict V).withDensity jacobianDensity.
```

The a.e. factorization rewrites the right side as

```text
(passiveSource.restrict V).withDensity (fun z => rawDensity (rawMap z)).
```

Pushing forward through `rawMap` and using the standard `withDensity`
pushforward formula gives

```text
Measure.map rawMap
  ((passiveSource.restrict V).withDensity
    (fun z => rawDensity (rawMap z)))
=
(Measure.map rawMap (passiveSource.restrict V)).withDensity rawDensity.
```

Therefore

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (passiveSource.restrict V)).withDensity rawDensity.
```

## Boundary

This is the exact identity available before proving determinant-chart Haar
transport for the passive-product theta measure.  To obtain the stronger raw
Haar statement needed by the formal-product source-reference bridge, one still
has to identify

```text
Measure.map rawMap (passiveSource.restrict V)
```

or the corresponding determinant-chart endpoint image with the correct raw
Haar restriction, including normalization and image equality up to null sets.

No source-image coverage, source-rank coverage, original source-prior
transport, normal-crossing theorem, pole-order computation, or RLCT extraction
is proved here.
