# Statement card - A2 Case 2 with-following endpoint reference image support

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Names:

```text
case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image
```

## Claim

For the enlarged Case 2 endpoint topology-tuple map `Y`, the named endpoint
reference image measure supported by a measurable source set `Ω` is unchanged
after restricting to the actual image `Y '' Ω`.  Equivalently, the unfolded
pushforward `Measure.map Y (referenceSource.restrict Ω)` is the named endpoint
reference image measure restricted to this actual image.

## Inputs

- finite source index types `ρ`, `τ`, and target tuple index family `κ'`;
- Case 2 bounds `hS`, `hcont`, and `hnext`;
- endpoint reindexing equivalences `eNext` and `e`;
- signed-box radii `Rres`;
- a source set `Ω`;
- `hΩ : MeasurableSet Ω`;
- `himage : MeasurableSet (Y '' Ω)`.

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

The unfolded equality theorem is:

```text
Measure.map Y (referenceSource.restrict Ω) =
  endpointReferenceImage.restrict (Y '' Ω).
```

## Dependencies

- `case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure`;
- `continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple`;
- `measure_map_restrict_image_eq_self_of_aemeasurable`.

## Nonclaims

No determinant-chart Haar equality, no raw-Haar transport, no raw-order
composition, no source-image coverage beyond `Y '' Ω`, no formal-product
domination, no normal crossings, no pole order, and no RLCT extraction.
