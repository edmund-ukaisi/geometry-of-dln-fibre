# Statement card - A2 Case 2 with-following endpoint reference image pivot-measurable support

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Names:

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self_of_subset_pivotNonzero
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image_of_subset_pivotNonzero
```

## Claim

For a measurable source set `Ω` contained in the selected-pivot-nonzero locus,
the named endpoint reference image measure for the enlarged Case 2 endpoint
map `Y` is unchanged after restriction to the actual image `Y '' Ω`.  The
unfolded pushforward equality also holds without a separately supplied
`MeasurableSet (Y '' Ω)` hypothesis.

## Inputs

- finite source index types `ρ`, `τ`, and target tuple index family `κ'`;
- `[DecidableEq ρ]`;
- source `OpensMeasurableSpace`, `BorelSpace`, and `PolishSpace` instances,
  using the default product measurable space convention;
- endpoint target `MeasurableSpace`, `OpensMeasurableSpace`, `BorelSpace`, and
  `T2Space` instances;
- Case 2 bounds `hS`, `hcont`, and `hnext`;
- endpoint reindexing equivalences `eNext` and `e`;
- signed-box radii `Rres`;
- a source set `Ω`;
- `hΩ : MeasurableSet Ω`;
- `hΩpivot : Ω ⊆ {z | case2PassiveThetaPivotNonzero n hS hnext z.1}`.

## Output

The support theorem is:

```text
endpointReferenceImage.restrict (Y '' Ω) = endpointReferenceImage
```

where

```text
endpointReferenceImage =
  case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
    n hS hcont hnext eNext e Rres Ω.
```

The unfolded theorem is:

```text
Measure.map Y (referenceSource.restrict Ω) =
  endpointReferenceImage.restrict (Y '' Ω).
```

## Dependencies

- `measurableSet_case2PassiveThetaWithFollowingFactorEndpointSectorSet_of_subset_pivotNonzero`;
- `case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self`;
- `measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image`.

## Nonclaims

No local change-of-variables formula, no Jacobian determinant theorem, no
determinant-chart Haar equality, no raw-Haar transport, no raw-order
composition, no source-image coverage beyond the actual image `Y '' Ω`, no
formal-product domination, no normal crossings, no pole order, and no RLCT
extraction.
