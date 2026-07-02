# Statement Card - A2 Case 2 with-following endpoint reference image domination

## Statement

If a source-domain measure is dominated by a scalar multiple of the concrete
with-following coordinate reference source,

```text
sourceMeasure <= d • referenceSource,
```

then for any source set `Omega`,

```text
Measure.map Y (sourceMeasure.restrict Omega)
  <=
d • endpointReferenceImage,
```

where

```text
endpointReferenceImage =
  case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
    ... Rres Omega
```

and

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    ... z eNext e.
```

## Kill Condition

The claim would fail if the endpoint reference image were not defined as
`Measure.map Y (referenceSource.restrict Omega)`, or if `Y` were not
a.e.-measurable for the restricted reference source.  It would also become an
overclaim if the target were replaced by determinant-chart Haar without a
separate endpoint COV theorem.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- Definition of
  `case2PassiveThetaWithFollowingFactorReferenceSourceMeasure`.
- Definition of
  `case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure`.
- Continuity of
  `case2PassiveThetaWithFollowingFactorEndpointTopologyTuple`.
- Restriction monotonicity and scalar restriction.
- `map_le_smul_map_of_le_smul_aemeasurable`.

## Lean Target

```text
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_sourceMeasure_restrict_le_smul_endpointReferenceImage_of_sourceMeasure_le_smul_referenceSource
```

## Nonclaims

No endpoint determinant-chart Haar domination, no endpoint Haar equality, no
full endpoint product COV, no raw-map pushforward, no raw-order Jacobian
insertion, no formal-product/source-image domination, no source-image
coverage, no normal crossings, no pole order, and no RLCT extraction.
