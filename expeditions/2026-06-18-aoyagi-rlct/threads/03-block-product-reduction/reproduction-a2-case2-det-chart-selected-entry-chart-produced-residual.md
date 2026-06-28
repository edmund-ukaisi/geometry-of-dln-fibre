# A2 Case 2 Determinant-Chart Selected-Entry Chart-Produced Residual

## Claim

In the two-edge Case 2 endpoint-transport lane, set

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center,
retainedData y =
  (case2PostPivotSelectedEntryRetainedPassiveData n hS hcont hnext y eNext)
    .endpointTransport e,
chart y = topologyTuple (retainedData y),
Sdet = topologyTupleDetChartSet,
signedBox = product_i volume.restrict (-Rres_i, Rres_i),
weightedBox = signedBox.withDensity (ofReal (sourceDensity pivotNext)),
muDet = Measure.map chart weightedBox.
```

Then, under the usual positive radii and selected-entry exponent condition,
the retained-passive p.13 determinant-chart residual is positive `muDet`-a.e.
and its negative `t`-power has finite lower integral against `muDet`.

This is the chart-produced version of the existing theorem with supplied
determinant-chart pushforward.  It proves only the local chart-produced
measure statement.  It does not identify Haar measure, an external source
prior, the full determinant chart, source-rank coverage, normal crossings,
pole order, or RLCT.

## Reproduction

The existing supplied-map theorem already proves the residual statement from a
measure identity

```text
m.restrict Sdet = Measure.map chart weightedBox.
```

For the chart-produced measure, take

```text
m = muDet = Measure.map chart weightedBox.
```

It remains to prove

```text
muDet.restrict Sdet = muDet.
```

This is a support statement, not a Jacobian statement.

For every coordinate vector `y`, the endpoint-transported selected-entry datum
lies in the retained-passive determinant chart:

```text
(retainedData y).detChart
```

by

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart.
```

Since `chart y = topologyTuple (retainedData y)`, the definition of
`topologyTupleDetChartSet` gives

```text
chart y in Sdet.
```

The chart is continuous by composing continuity of the selected-entry datum,
endpoint transport, and `topologyTuple`, so it is a.e. measurable for
`signedBox`.  Because `weightedBox` is obtained from `signedBox` by
`withDensity`, it is absolutely continuous with respect to `signedBox`; hence
the same chart is a.e. measurable for `weightedBox`.

The set `Sdet` is measurable because it is open:

```text
isOpen_topologyTupleDetChartSet.measurableSet.
```

The pointwise inclusion `chart y in Sdet` gives

```text
forall^ae z with respect to Measure.map chart weightedBox, z in Sdet.
```

Using `Measure.restrict_eq_self_of_ae_mem`, this proves

```text
muDet.restrict Sdet = muDet.
```

Substituting this identity into the supplied-map theorem gives the desired
positivity and finite-integral statement over `muDet` itself.

## Boundary

The proof deliberately avoids the false global reading

```text
arbitrary m.restrict Sdet = Measure.map chart weightedBox.
```

The statement fixes the target measure to the chart-produced measure
`Measure.map chart weightedBox`.  Any theorem for Haar measure or for an
external source prior needs a separate image/coverage/prior-transport theorem.
