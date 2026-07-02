# Statement card - A2 with-following endpoint selected-entry source density

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
```

Names:

```text
case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_eq_unweighted_withDensity_selectedEntrySourceDensity
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_unweighted_withDensity_selectedEntrySourceDensity_restrict_eq_endpointReferenceImageMeasure
```

## Claim

The enlarged Case 2 endpoint reference source is the unweighted
passive/center/following coordinate-product source with exactly the
selected-entry source-density factor.  Consequently, pushing that weighted
unweighted source through the enlarged endpoint topology-tuple map gives the
named endpoint reference image measure.

## Proved

Lean proves the source-measure identity

```text
referenceSource =
  unweightedSource.withDensity selectedEntrySourceDensity
```

and the endpoint-image pushforward identity

```text
Measure.map Y
  ((unweightedSource.withDensity selectedEntrySourceDensity).restrict Omega)
  =
endpointReferenceImage.
```

## Assumed

Only the finite type and measurability instances required by the existing
coordinate-product measures and endpoint image definition.

## Cited

None.

## Deferred

No determinant-chart Haar equality, no raw-order Haar equality, no full target
coverage theorem, no source-prior transport, no normal crossings, no pole
order, and no RLCT extraction.

## Structure & Ideas Observed

The selected-entry density is already present in the existing
`case2PassiveThetaCenterWeightedBoxMeasure`.  The proof is a product-measure
reassociation:

```text
passiveRef × (signedBox.withDensity density)
  =
(passiveRef × signedBox).withDensity (density after snd),
```

then the same formula through the independent following-factor product.

## Route

Use Mathlib's `prod_withDensity_right₀` and `prod_withDensity_left₀`, with
the existing selected-entry a.e.-measurability package
`SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds`.
The endpoint image theorem then follows by unfolding the named endpoint
reference image and substituting the source-measure identity.

## Status

Sorry-free and reviewed.
