# Statement Card - A2 Case 2 with-following endpoint reference image active-readout marginal

## Statement

For the named enlarged endpoint reference image measure with unrestricted
source domain,

```text
endpointReferenceImage =
  case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
    ... Rres Set.univ,
```

the active-coordinate readout has product marginal

```text
Measure.map activeReadout endpointReferenceImage
  =
(passiveRef.prod
  (volume.restrict (chartMap pivotNext '' signedBoxSet Rres))).prod
followingRef.
```

The map `activeReadout` is the finite endpoint-coordinate readout defined on
`TopologyTuple`; it reads the passive fields, the selected-entry charted
successor residual coordinates, and the independent following factor.

## Kill Condition

The claim would be false if the endpoint image were restricted to an arbitrary
non-rectangular source set, because the active marginal need not remain the
unrestricted product measure.  The claim would also fail without measurability
of `activeReadout` and `Y`, since the proof uses `Measure.map_map`.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- Definition of
  `case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure`.
- Continuity of
  `case2PassiveThetaWithFollowingFactorEndpointTopologyTuple`.
- Continuity of
  `Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout`.
- Composite product COV:
  `measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_activeReadout_comp_referenceSource_eq_prod`.

## Lean Targets

```text
Case2PassiveThetaWithFollowingFactor.continuous_endpointTopologyTupleActiveReadout
measure_map_case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_activeReadout_univ_eq_prod
```

## Nonclaims

No endpoint determinant-chart Haar equality, no equality of the full endpoint
image measure with a product/reference measure, no raw-map pushforward, no
raw-order Jacobian insertion, no formal-product/source-image domination, no
source-image coverage, no localized arbitrary-source-set product marginal, no
normal crossings, no pole order, and no RLCT extraction.
