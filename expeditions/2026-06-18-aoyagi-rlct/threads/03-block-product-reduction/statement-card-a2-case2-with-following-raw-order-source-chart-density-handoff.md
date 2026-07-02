# Statement Card - A2 Case 2 with-following raw-order source-chart density handoff

## Statement

Near any enlarged Case 2 determinant-sector point with nonzero selected pivot,
inside any prescribed open theta-neighborhood `G`, there is a smaller open set
`V` such that

```text
rawChart (rawMap z) = sourceChart z  for z in V.
```

For every theta-domain measure `thetaReference` and raw density `rawDensity`,
if

```text
AEMeasurable rawMap (thetaReference.restrict V)
AEMeasurable rawDensity
  (Measure.map rawMap (thetaReference.restrict V)),
```

then

```text
Measure.map rawChart
  ((Measure.map rawMap (thetaReference.restrict V)).withDensity rawDensity)
=
Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

## Kill Condition

The theorem depends on the existing local two-stage equality between
`rawChart ∘ rawMap` and `sourceChart` after restriction to `V`, plus the generic
map/withDensity handoff.  Without a.e. measurability for `rawMap` and
`rawDensity`, the `withDensity` pushforward rewrite is not available.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- With-following raw-order/source-chart bridge:
  `exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse`.
- Generic measure handoff:
  `measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict`.

## Lean Target

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpoint_rawOrderSourceChart_withDensity_eq_sourceChart_withDensity
```

## Nonclaims

No determinant-chart Haar equality, no endpoint Haar transport, no raw-order
Haar transport, no constructed Jacobian density, no external/original
source-prior identification, no source-image coverage, no raw-map pushforward
to Haar, no normal crossings, no pole order, and no RLCT extraction.
