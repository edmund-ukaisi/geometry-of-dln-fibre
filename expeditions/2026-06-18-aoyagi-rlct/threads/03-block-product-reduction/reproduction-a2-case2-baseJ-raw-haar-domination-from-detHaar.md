# Reproduction - A2 Case 2 baseJ raw-Haar domination from determinant Haar

Date: 2026-07-01.

Status: pen-and-paper reproduction for the formal-product weighted raw-order
domination socket.

## Question

Assume the endpoint topology-tuple pushforward of the unweighted Case 2
passive-product theta source is dominated on the retained-passive determinant
chart:

```text
Measure.map Y (passiveSource.restrict V)
  <= c • rawHaar.restrict rawDetChart.
```

What does this imply for the globally Jacobian-weighted reference

```text
baseJ = passiveSource.withDensity jacobianDensity,
```

where

```text
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))?
```

## Calculation

Let

```text
Phi y = topologyTupleEdgeRawOrder y

formalDensity y =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt y).
```

On the local Case 2 determinant/pivot sector, `rawMap = Phi ∘ Y` and

```text
baseJ.restrict V
=
(passiveSource.restrict V).withDensity (fun z => formalDensity (Y z)).
```

The determinant-chart domination is a domination of measures on the raw tuple
space before applying `Phi`.  Weight both sides by the same formal-product
density:

```text
(Measure.map Y (passiveSource.restrict V)).withDensity formalDensity
  <= c • ((rawHaar.restrict rawDetChart).withDensity formalDensity).
```

The generic weighted composed-map lemma rewrites the left side before applying
`Phi` as the pushforward of the weighted theta reference:

```text
Measure.map (fun z => Phi (Y z))
  ((passiveSource.restrict V).withDensity (formalDensity ∘ Y)).
```

Aoyagi's retained-passive raw-order formal-product change of variables gives
the reference-side identity

```text
Measure.map Phi ((rawHaar.restrict rawDetChart).withDensity formalDensity)
  =
rawHaar.restrict rawSourceSet.
```

Therefore

```text
Measure.map rawMap (baseJ.restrict V)
  <= c • rawHaar.restrict rawSourceSet.
```

## Boundary

This gives the same-scalar raw-Haar form for `baseJ`: the formal-product
density in `baseJ` is exactly the density whose raw-order change of variables
turns determinant-chart Haar into restricted raw-source Haar.

The determinant-chart domination hypothesis remains unchanged and explicit.
Since `passiveMeasure` is arbitrary, the theorem does not prove that
hypothesis.  It does not prove exact raw-Haar pushforward for the unweighted
passive source, passive-product Haar transport, raw-Haar normalization,
original source-prior transport, source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction.
