# Statement Card - A2 Case 2 baseJ raw-Haar domination from determinant Haar

## Claim

On a local Case 2 passive-theta determinant/pivot sector, if the endpoint
topology-tuple pushforward of the unweighted passive-product theta reference is
dominated by additive Haar on the retained-passive determinant chart,

```text
Measure.map Y (passiveSource.restrict V)
  <= c • rawHaar.restrict rawDetChart,
```

then the raw-order pushforward of the globally Jacobian-weighted reference

```text
baseJ = passiveSource.withDensity jacobianDensity
```

is dominated by the same scalar multiple of additive Haar restricted to the
raw-order source-recursive determinant chart:

```text
Measure.map rawMap (baseJ.restrict V)
  <= c • rawHaar.restrict rawSourceSet.
```

Here

```text
rawMap z = topologyTupleEdgeRawOrder (Y z)

jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)).
```

## Inputs Used

- the local Case 2 determinant/pivot sector theorem, to choose
  `V subset G`;
- continuity/a.e.-measurability of the endpoint topology-tuple map `Y`;
- a.e.-measurability of the retained-passive formal-product density on
  `rawHaar.restrict rawDetChart`;
- a.e.-measurability of `topologyTupleEdgeRawOrder` after weighting the
  determinant-chart Haar reference by that formal-product density;
- the exact retained-passive raw-order formal-product change-of-variables
  theorem

```text
Measure.map Phi ((rawHaar.restrict rawDetChart).withDensity formalDensity)
  =
rawHaar.restrict rawSourceSet;
```

- the generic weighted composed-map domination lemma.

## Output

This packages the `baseJ` measure in the strongest currently available
raw-Haar form.  Compared with the earlier inverse-Jacobian domination socket,
there is no extra local `K` and no target-side inverse-Jacobian density in the
conclusion, because `baseJ` already includes the formal-product determinant
factor used by the raw-order change of variables.

## Nonclaims

The determinant-chart domination remains an explicit hypothesis.  The theorem
does not prove exact raw-Haar pushforward for the unweighted passive source,
passive-product Haar transport, raw-Haar normalization, original source-prior
transport, source-image coverage, source-rank coverage, normal crossings, pole
order, or RLCT extraction.
