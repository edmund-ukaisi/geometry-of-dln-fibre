# Reproduction - A2 with-following formal product dominated by reference source from determinant domination

Date: 2026-07-07.

## Claim

On the usual with-following Case 2 passive-theta local chart, assume the
determinant-side reverse domination

```text
rawHaar.restrict rawDetChart
  <= Cdet • Measure.map Y (referenceSource.restrict V).
```

Here `Y` is the with-following endpoint topology-tuple map.  Then, after
shrinking around the base point, the p.13 formal-product measure on any chart
piece inside `p13SourceSet` is dominated by the source-chart reference measure

```text
Measure.map sourceChart (referenceSource.restrict V)
```

with scalar `Cdet * CJ`, where `CJ` is a finite local upper bound for the
retained-passive raw-order Jacobian density.

## Pen-And-Paper Check

Let

```text
j(z) = ofReal retainedPassiveFormalRawOrderJacobianProductAbsDetAt(Y z)
baseJ = referenceSource.withDensity j
rawMap(z) = topologyTupleEdgeRawOrder(Y z).
```

The existing with-following raw-image handoff says that, on a local shrink
`Vraw`, determinant reverse domination transfers to raw-source domination for
the weighted source:

```text
rawHaar.restrict rawSourceSet
  <= Cdet • Measure.map rawMap (baseJ.restrict Vraw).
```

The local Jacobian-bound theorem supplies a finite `CJ` and an eventual
neighborhood bound

```text
j(z) <= CJ.
```

Shrink once more to an open `V` contained in `Vraw` on which this bound holds
pointwise.  Then it holds a.e. for `referenceSource.restrict V`, and the
standard bounded-density lemma gives

```text
baseJ.restrict V
  = (referenceSource.withDensity j).restrict V
  <= CJ • referenceSource.restrict V.
```

The raw map is a.e. measurable for `baseJ.restrict V` by the raw-image handoff,
and the same local continuity makes it a.e. measurable for
`referenceSource.restrict V`.  Mapping the bounded-density domination through
`rawMap` gives

```text
Measure.map rawMap (baseJ.restrict V)
  <= CJ • Measure.map rawMap (referenceSource.restrict V).
```

The same-shrink order is important.  First take the open shrink `Vform` from
the formal-product/source-reference socket.  Then run the raw-image handoff
inside `Vform` intersected with the open neighborhood on which `j <= CJ`; this
returns the smaller open `V subset Vform`.  Feed the formal socket with

```text
thetaReference := referenceSource.restrict V.
```

Since `V subset Vform`,

```text
(referenceSource.restrict V).restrict Vform = referenceSource.restrict V.
```

Thus the raw-source domination needed by the formal socket is exactly the one
obtained after composing the determinant handoff with the bounded-density map
comparison:

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * CJ) • Measure.map rawMap (referenceSource.restrict V).
```

Finally the with-following formal-product/source-reference socket consumes
exactly this raw-source domination and returns, for every
`chartPiece subset p13SourceSet`,

```text
formalProductMeasure.restrict chartPiece
  <= (Cdet * CJ) • Measure.map sourceChart (referenceSource.restrict V).
```

## Boundary

The determinant-side reverse domination remains an explicit hypothesis.  This
does not prove determinant-chart Haar transport, exact raw-Haar pushforward,
source-prior or original-prior transport, source coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction.  The only new
composition is the local Jacobian upper bound which converts the already
weighted source measure `baseJ` back to the unweighted reference source.
