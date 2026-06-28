# A2 Retained-Passive Selected-Entry Chart-Produced Determinant Residual

## Claim

The generic retained-passive selected-entry determinant residual handoff has a
chart-produced version.

Let

```text
S = topologyTupleDetChartSet,
signedBox = product_i volume.restrict (-Rres_i, Rres_i),
weightedBox = signedBox.withDensity (ofReal (sourceDensity pivot)),
targetMeasure = Measure.map chart weightedBox.
```

Assume:

- `chart` is a.e. measurable on `signedBox`;
- `S` is measurable;
- `chart y in S` for every selected-entry coordinate vector `y`;
- the retained-passive direct residual positive set is measurable;
- the direct residual readout through `chart` is the selected-entry residual.

Then the retained-passive p.13 determinant residual is positive
`targetMeasure`-a.e. and has finite negative `t`-power lower integral with
respect to `targetMeasure`, under the usual positive radii and selected-entry
exponent condition.

## Reproduction

The existing supplied-map theorem proves the desired residual statement from

```text
m.restrict S = Measure.map chart weightedBox.
```

For the chart-produced theorem, instantiate

```text
m = targetMeasure = Measure.map chart weightedBox.
```

It remains to show

```text
targetMeasure.restrict S = targetMeasure.
```

Because `weightedBox` is obtained from `signedBox` by `withDensity`, it is
absolutely continuous with respect to `signedBox`.  Therefore the supplied
a.e. measurability of `chart` on `signedBox` gives a.e. measurability of
`chart` on `weightedBox`.

The assumptions `MeasurableSet S` and `forall y, chart y in S` give, by
`ae_map_iff`,

```text
forall^ae z with respect to Measure.map chart weightedBox, z in S.
```

Applying `Measure.restrict_eq_self_of_ae_mem` yields the required support
identity.  The supplied-map theorem then gives residual positivity and finite
negative-power integral on `targetMeasure.restrict S`; rewriting by the support
identity gives the result on `targetMeasure`.

## Boundary

This theorem is a support wrapper for chart-produced measures only.  It does
not identify Haar measure, an external source prior, full determinant-chart
coverage, local loss or density bounds, source-rank coverage, normal crossings,
pole order, or RLCT.
