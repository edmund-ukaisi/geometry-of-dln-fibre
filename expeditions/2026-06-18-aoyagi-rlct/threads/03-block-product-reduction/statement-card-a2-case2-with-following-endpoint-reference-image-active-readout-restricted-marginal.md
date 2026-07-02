# Statement Card - A2 Case 2 with-following endpoint reference image restricted active-readout marginal

## Statement

For any source set `Omega`, the active-coordinate readout of the named
endpoint reference image equals the active selected-entry chart pushforward of
the same restricted source reference:

```text
Measure.map activeReadout
  (case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
    ... Rres Omega)
  =
Measure.map activeChart
  (referenceSource.restrict Omega).
```

Here

```text
activeChart z
  = ((z.1.1, chartMap pivotNext z.1.yNext), z.2).
```

## Kill Condition

The claim would be false if `activeReadout (Y z)` did not equal `activeChart
z` pointwise.  A stronger product-measure conclusion would be false for a
general non-rectangular `Omega`; the statement intentionally keeps the
restricted source pushforward on the right.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- Definition of
  `case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure`.
- Continuity of
  `case2PassiveThetaWithFollowingFactorEndpointTopologyTuple`.
- Continuity of
  `Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout`.
- Pointwise composite identity
  `Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart`.
- `Measure.map_map`.

## Lean Targets

```text
measure_map_case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_activeReadout_eq_activeSelectedEntryChart_restrict
```

## Nonclaims

No unrestricted product marginal for arbitrary `Omega`, no endpoint
determinant-chart Haar equality, no equality of the full endpoint image
measure with a product/reference measure, no raw-map pushforward, no raw-order
Jacobian insertion, no formal-product/source-image domination, no source-image
coverage, no normal crossings, no pole order, and no RLCT extraction.
