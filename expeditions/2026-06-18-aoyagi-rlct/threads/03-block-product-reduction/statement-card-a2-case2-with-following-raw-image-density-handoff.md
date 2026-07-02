# Statement Card - A2 Case 2 with-following raw-image density handoff

## Statement

Near any enlarged Case 2 determinant-sector point with nonzero selected pivot,
inside any prescribed open theta-neighborhood `G`, there is a smaller open set
`V` such that the endpoint topology tuple lies in the determinant chart and
the raw-order map is continuous on `V`.

For any with-following source-domain measure `sourceMeasure`, define

```text
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))

baseJ = sourceMeasure.withDensity jacobianDensity.
```

If a supplied raw density satisfies

```text
AEMeasurable rawDensity
  (Measure.map rawMap (sourceMeasure.restrict V))

jacobianDensity z = rawDensity (rawMap z)
```

for `sourceMeasure.restrict V`-a.e. `z`, then

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (sourceMeasure.restrict V)).withDensity rawDensity.
```

## Kill Condition

The theorem needs the local determinant-chart shrink so that `rawMap` is
a.e.-measurable on `sourceMeasure.restrict V`.  It also needs the explicit
a.e. factorisation of `jacobianDensity` through `rawMap`; without that
factorisation, the generic `withDensity` pushforward lemma cannot identify the
raw-side density.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- With-following local raw-order/source-chart bridge:
  `exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse`.
- Continuity of the enlarged endpoint topology tuple:
  `continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple`.
- Generic measure handoff:
  `measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq`.

## Lean Target

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_eq_withDensity_rawImage_of_jacobianDensity_ae_eq
```

## Nonclaims

No determinant-chart Haar equality, no endpoint Haar transport, no raw-order
Haar transport, no constructed raw density, no external/original source-prior
identification, no source-image coverage, no raw-map pushforward to Haar, no
normal crossings, no pole order, and no RLCT extraction.
