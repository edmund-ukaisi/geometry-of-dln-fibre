# Statement Card - A2 Case 2 with-following raw-image inverse-readback density

## Statement

Near any enlarged Case 2 determinant-sector point with nonzero selected pivot,
inside any prescribed open theta-neighborhood `G`, there is a smaller open set
`V` such that the raw-order map lands in the raw-order determinant source set.

For any with-following source-domain measure `sourceMeasure`, define

```text
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))

baseJ = sourceMeasure.withDensity jacobianDensity

rawDensity y =
  ofReal
    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
      (topologyTupleEdgeRawOrderInverse y)).
```

Then

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (sourceMeasure.restrict V)).withDensity rawDensity.
```

The equality is relative to the actual raw-image measure
`Measure.map rawMap (sourceMeasure.restrict V)`.

## Kill Condition

The proof needs the local shrink where `Y z` is in the determinant chart and
`rawMap z` is in the raw-order determinant source set.  Without this support,
the inverse-readback density is not known to be a.e.-measurable on the raw
image and the inverse identity
`topologyTupleEdgeRawOrderInverse (rawMap z) = Y z` is unavailable.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- With-following local raw-order/source-chart bridge:
  `exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse`.
- Raw-order inverse continuity and inverse identity on determinant charts.
- Generic measure handoff:
  `measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq`.

## Lean Target

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_eq_withDensity_rawImage_rawOrderInverse_jacobianDensity
```

## Nonclaims

No determinant-chart Haar equality, no endpoint Haar transport, no raw-order
Haar transport, no target-side inverse Jacobian density theorem, no global
Radon-Nikodym derivative, no external/original source-prior identification, no
source-image coverage, no raw-map pushforward to Haar, no normal crossings, no
pole order, and no RLCT extraction.
