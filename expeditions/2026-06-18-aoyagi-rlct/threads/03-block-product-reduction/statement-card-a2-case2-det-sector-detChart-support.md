# Statement Card - A2 Case 2 determinant-sector determinant-chart support

## Claim

For the concrete Case 2 full passive-theta endpoint topology-tuple map `Y`, if
a measurable theta-domain set `Omega` is contained in
`case2PassiveThetaDetSector`, then for any theta measure,

```text
(Measure.map Y (thetaMeasure.restrict Omega)).restrict rawDetChart
  = Measure.map Y (thetaMeasure.restrict Omega),
```

where

```text
rawDetChart = topologyTupleDetChartSet.
```

Public Lean name:

```text
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_detChartSet_eq_self_of_subset_detSector
```

## Inputs Used

- measurability of `Omega`;
- `Omega subset case2PassiveThetaDetSector`;
- a.e. measurability of the endpoint topology-tuple map on
  `thetaMeasure.restrict Omega`;
- openness, hence measurability, of `topologyTupleDetChartSet`;
- pointwise theorem
  `case2PassiveThetaEndpointTopologyTuple_mem_detChartSet`.

## Output

This supplies the determinant-chart support side needed by a future concrete
passive-reference COV theorem.  It says that once the theta source is localized
inside the passive determinant sector, its endpoint retained-passive
topology-tuple image is supported on the determinant chart.

## Nonclaims

The theorem does not construct the passive reference measure, compute the
Jacobian of `Y`, prove determinant-chart Haar transport, prove domination by
Haar, normalize Haar scalars, identify an original source prior, prove
source-image coverage, prove source-rank coverage, construct normal crossings,
compute pole order, or extract an RLCT.
