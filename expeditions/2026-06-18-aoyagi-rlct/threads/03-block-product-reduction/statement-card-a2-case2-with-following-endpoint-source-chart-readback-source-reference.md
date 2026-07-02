# Statement Card - A2 Case 2 with-following endpoint source-chart readback source reference

## Statement

Near any enlarged Case 2 determinant-sector point with nonzero selected pivot,
inside any prescribed open theta-neighborhood `G`, there is a smaller open set
`V` such that the with-following endpoint source chart is injective and
continuous on `V`, has measurable image, and for every theta-domain measure
`thetaReference`,

```text
let sourceRef =
  Measure.map sourceChart (thetaReference.restrict V)

AEMeasurable readback sourceRef
  and
Measure.map readback sourceRef = thetaReference.restrict V.
```

## Kill Condition

The claim would fail without the pointwise local left inverse

```text
readback (sourceChart z) = z  for z in V,
```

or without the local injective/continuous source-chart image package needed to
make `readback` a.e.-measurable for the chart-produced source measure.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- Existing with-following local source-chart image theorem:
  `exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse`.
- `aemeasurable_readback_map_sourceChart_restrict_of_continuousOn_injOn_leftInverse`.
- `measure_map_readback_map_sourceChart_restrict_eq_self_of_aemeasurable`.

## Lean Target

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointSourceChart_map_readback_sourceReference_eq_self
```

## Nonclaims

No local `Y` change of variables, no determinant-chart Haar equality, no
endpoint Haar transport, no external/original source-prior identification, no
source-image coverage, no density comparison, no raw-map pushforward, no
normal crossings, no pole order, and no RLCT extraction.
