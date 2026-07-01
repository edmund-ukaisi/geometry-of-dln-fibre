# Statement Card - A2 Case 2 source-chart source-reference readback

## Claim

On the local passive-theta endpoint source-chart image, the chart-produced
source reference pulls back exactly to the restricted theta reference.

Public Lean name:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_sourceReference_eq_self
```

## Inputs Used

- the local source-chart image theorem giving an open `V`, left inverse,
  injectivity, continuity, and measurable source image;
- `aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse`;
- `measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable`.

## Output

For every theta reference measure, with

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V),
```

Lean proves:

```text
AEMeasurable readback sourceRef
Measure.map readback sourceRef = thetaReference.restrict V.
```

## Nonclaims

This identifies only the chart-produced source reference.  It does not identify
an original source prior, prove density bounds, prove source-image coverage,
transport Haar measure, establish normal crossings, compute pole order, or
extract an RLCT.
