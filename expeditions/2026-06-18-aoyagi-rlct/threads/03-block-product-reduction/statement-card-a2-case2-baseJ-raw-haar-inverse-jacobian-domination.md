# Statement Card - A2 Case 2 baseJ raw-Haar inverse-Jacobian domination

## Claim

On a local Case 2 passive-theta determinant/pivot sector, there is a constant
`K > 0` and an open `V subset G` such that, for every additive Haar measure
`rawHaar` and scalar `c`, the explicit determinant-chart domination hypothesis

```text
Measure.map Y (passiveSource.restrict V)
  <= c • rawHaar.restrict rawDetChart
```

implies

```text
Measure.map rawMap (baseJ.restrict V)
  <= (ofReal K * c) • ((rawHaar.restrict rawSourceSet).withDensity
    rawInverseJacobianDensity).
```

Here

```text
baseJ = passiveSource.withDensity jacobianDensity
```

and

```text
rawInverseJacobianDensity y =
  ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y).
```

## Inputs Used

- the local Case 2 Jacobian sandwich for the forward retained-passive formal
  raw-order Jacobian product;
- the conditional passive-source raw-Haar inverse-Jacobian domination socket;
- `Measure.restrict_restrict_of_subset`, `restrict_withDensity`, and
  `Measure.restrict_smul` to pass the `U`-bound down to `V`;
- `map_le_smul_map_of_le_smul_aemeasurable`;
- scalar-composition bookkeeping.

## Output

This packages the globally Jacobian-weighted reference `baseJ` for later raw
Haar consumers, while keeping the unweighted determinant-chart comparison as
the visible frontier.

## Nonclaims

The theorem does not prove the determinant-chart domination hypothesis.  It
does not prove exact raw-Haar pushforward, passive-product Haar transport,
raw-Haar normalization, original source-prior transport, source-image
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction.
