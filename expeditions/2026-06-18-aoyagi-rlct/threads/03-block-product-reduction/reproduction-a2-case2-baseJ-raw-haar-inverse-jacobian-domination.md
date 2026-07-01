# Reproduction - A2 Case 2 baseJ raw-Haar inverse-Jacobian domination

Date: 2026-07-01.

Status: pen-and-paper reproduction for a bounded-density conditional socket.

## Question

Given the conditional raw-Haar domination socket for the unweighted passive
source, what can be said about the globally Jacobian-weighted source

```text
baseJ = passiveSource.withDensity jacobianDensity?
```

## Calculation

The already-proved Case 2 Jacobian sandwich gives a local open set `U` and a
constant `K > 0` such that

```text
(passiveSource.restrict U).withDensity jacobianDensity
  <= ofReal K • passiveSource.restrict U.
```

Shrink the raw-order socket inside `G ∩ U`; it returns an open
`V subset G ∩ U`.  Since `V subset U`,

```text
baseJ.restrict V
=
(passiveSource.withDensity jacobianDensity).restrict V
=
((passiveSource.restrict U).withDensity jacobianDensity).restrict V
<=
(ofReal K • passiveSource.restrict U).restrict V
=
ofReal K • passiveSource.restrict V.
```

Mapping by `rawMap` preserves this domination:

```text
Measure.map rawMap (baseJ.restrict V)
  <= ofReal K • Measure.map rawMap (passiveSource.restrict V).
```

The unweighted conditional raw-Haar socket says that, under the explicit
determinant-chart domination

```text
Measure.map Y (passiveSource.restrict V)
  <= c • rawHaar.restrict rawDetChart,
```

we have

```text
Measure.map rawMap (passiveSource.restrict V)
  <= c • ((rawHaar.restrict rawSourceSet).withDensity
    rawInverseJacobianDensity).
```

Composing the two scalar dominations gives

```text
Measure.map rawMap (baseJ.restrict V)
  <= (ofReal K * c) • ((rawHaar.restrict rawSourceSet).withDensity
    rawInverseJacobianDensity).
```

## Boundary

The determinant-chart domination hypothesis is unchanged and remains explicit.
The theorem only adds the local boundedness of the forward Jacobian density.
It does not prove passive-product Haar transport, exact raw-Haar pushforward,
raw-Haar normalization, original source-prior transport, source-image
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction.
