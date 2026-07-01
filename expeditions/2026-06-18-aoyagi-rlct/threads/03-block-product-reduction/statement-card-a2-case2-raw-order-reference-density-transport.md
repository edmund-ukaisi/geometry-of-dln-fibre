# Statement Card - A2 Case 2 raw-order reference density transport

## Claim

On the local Case 2 determinant/punctured-sector shrink, any a.e. measurable
raw density on the named raw-order reference image transports through the p.13
raw-order chart to the direct source-chart image of the theta-domain reference
source weighted by the composed density:

```text
Measure.map rawChart
  (rawOrderReferenceImage.withDensity rawDensity)
=
Measure.map sourceChart
  ((referenceSource.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

Expected public Lean name:

```text
exists_open_subset_case2PassiveThetaRawOrderReferenceImage_withDensity_sourceChart_handoff
```

## Inputs Used

- `case2PassiveThetaRawOrderReferenceImageMeasure`;
- the local raw-order/source-chart two-stage theorem;
- `measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict`;
- local a.e. measurability of `rawMap`;
- supplied a.e. measurability of `rawDensity` for the named raw-order image.

## Nonclaims

No raw-Haar identification, determinant-chart Haar transport, original
source-prior transport, bounded-density construction, source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction is
claimed.
