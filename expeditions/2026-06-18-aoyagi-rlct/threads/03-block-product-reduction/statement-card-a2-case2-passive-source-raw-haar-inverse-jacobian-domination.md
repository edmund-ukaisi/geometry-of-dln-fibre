# Statement Card - A2 Case 2 passive-source raw-Haar inverse-Jacobian domination

## Claim

On a local Case 2 passive-theta determinant/pivot sector, if the endpoint
topology-tuple pushforward of the unweighted passive-product theta reference is
dominated by additive Haar on the retained-passive determinant chart,

```text
Measure.map Y (passiveSource.restrict V)
  <= c • rawHaar.restrict rawDetChart,
```

then the raw-order pushforward is dominated by the same scalar multiple of the
raw-order Haar measure weighted by the retained-passive inverse-Jacobian
density:

```text
Measure.map rawMap (passiveSource.restrict V)
  <= c • ((rawHaar.restrict rawSourceSet).withDensity
    rawInverseJacobianDensity).
```

Here

```text
rawMap z =
  topologyTupleEdgeRawOrder (Y z)

rawInverseJacobianDensity y =
  ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y).
```

## Inputs Used

- the local Case 2 determinant/pivot sector theorem, only to choose
  `V subset G`;
- continuity/a.e.-measurability of the endpoint topology-tuple map `Y`;
- a.e.-measurability of `topologyTupleEdgeRawOrder` on
  `rawHaar.restrict rawDetChart`;
- the retained-passive raw-order inverse-Jacobian change-of-variables theorem;
- a generic composed-map domination lemma.

## Output

The theorem moves the current frontier from the nonlinear raw image to the
cleaner endpoint determinant-chart comparison:

```text
Measure.map Y (passiveSource.restrict V)
  <= c • rawHaar.restrict rawDetChart.
```

The Lean statement also returns

```text
AEMeasurable rawMap (passiveSource.restrict V),
```

so downstream wrappers can push scalar domination through `rawMap` without
reopening the local determinant-chart continuity proof.

## Nonclaims

The determinant-chart comparison is still an explicit hypothesis.  The theorem
does not prove exact raw-Haar pushforward, passive-product Haar transport,
raw-Haar normalization, original source-prior transport, source-image
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction.
