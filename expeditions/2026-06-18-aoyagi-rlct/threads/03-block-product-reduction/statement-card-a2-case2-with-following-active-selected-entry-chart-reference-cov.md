# Statement Card - A2 Case 2 with-following active selected-entry reference COV

## Statement

For the enlarged source-reference measure

```text
case2PassiveThetaWithFollowingFactorReferenceSourceMeasure n hS hnext Rres,
```

the source-coordinate map

```text
((passive, yNext), F) |-> ((passive, chartMap pivotNext yNext), F)
```

pushes the reference measure to

```text
(passiveRef.prod
  (volume.restrict (chartMap pivotNext '' signedBoxSet Rres))).prod
followingRef.
```

Generic product versions also hold for arbitrary s-finite side measures on the
right or on the left.

## Kill Condition

The claim would be false if the selected-entry one-chart weighted pushforward
were not stable under product with an arbitrary s-finite side measure, or if
the enlarged reference source were not definitionally the product of
passive-theta reference measure and following-factor reference measure.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- Existing Lean theorem
  `SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image`.
- Mathlib `Measure.map_prod_map`.
- Product reference definitions in
  `RetainedPassiveCase2PassiveThetaEndpointReference.lean` and
  `RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean`.

## Lean Targets

```text
SelectedEntrySignedBox.CenterCoord.map_prod_chartMap_id_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image_prod
SelectedEntrySignedBox.CenterCoord.map_prod_id_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_prod_restrict_image
sigmaFinite_case2PassiveThetaPassiveFieldReferenceMeasure
sFinite_case2PassiveThetaPassiveFieldReferenceMeasure
sFinite_case2PassiveThetaReferenceSourceMeasure
measure_map_case2PassiveThetaWithFollowingFactor_activeSelectedEntryChart_referenceSource_eq_prod
```

## Nonclaims

No endpoint determinant-chart Haar equality, no raw-map pushforward, no
raw-order Jacobian insertion, no formal-product/source-image domination, no
source-image coverage, no normal crossings, no pole order, and no RLCT
extraction.

