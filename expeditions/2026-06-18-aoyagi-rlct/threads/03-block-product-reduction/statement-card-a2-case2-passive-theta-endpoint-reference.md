# Statement Card - A2 Case 2 passive-theta endpoint reference

## Claim

Lean now names the concrete coordinate-product passive-theta reference source
measure for Aoyagi Case 2:

```text
case2PassiveThetaReferenceSourceMeasure
  = case2PassiveThetaPassiveFieldReferenceMeasure.prod
      case2PassiveThetaCenterWeightedBoxMeasure.
```

The passive-field factor is the product of entrywise Lebesgue measures on
`A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`.  The center factor is the
selected-entry weighted signed-box measure.

For a measurable local set `Omega` contained in
`case2PassiveThetaDetSector`, the endpoint topology-tuple pushforward of this
reference source is supported on `topologyTupleDetChartSet`.

Public Lean names:

```text
matrixEntryReferenceMeasure
case2PassiveThetaPassiveFieldReferenceMeasure
case2PassiveThetaCenterSignedBoxMeasure
case2PassiveThetaCenterWeightedBoxMeasure
case2PassiveThetaReferenceSourceMeasure
case2PassiveThetaEndpointReferenceImageMeasure
measure_map_case2PassiveThetaEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector
case2PassiveThetaEndpointReferenceImageMeasure_restrict_detChartSet_eq_self_of_subset_detSector
measure_map_case2PassiveThetaEndpointTopologyTuple_passiveSource_restrict_le_smul_endpointReferenceImage_of_passiveMeasure_le_smul_reference
```

## Inputs Used

- finite index types for matrix and center coordinates;
- the entrywise product measurable-space convention for matrices and products;
- measurability of the local set `Omega`;
- `Omega subset case2PassiveThetaDetSector`;
- continuity of `case2PassiveThetaEndpointTopologyTuple`;
- the previously proved support theorem
  `measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_detChartSet_eq_self_of_subset_detSector`.

## Output

This fixes the concrete passive-theta reference source and names its endpoint
image measure for later image-measure/bounded-density work.  It also proves
the support half: after determinant-sector localization, the endpoint image of
the reference is carried by the determinant chart.

It also proves the honest domination transfer: if a passive-field measure is
dominated by a scalar multiple of the concrete passive-field reference, then
the endpoint pushforward of the corresponding passive-product source is
dominated by the same scalar multiple of the named endpoint reference image
measure.

The unrestricted full determinant-chart Haar target is not the right next
claim for this theta domain: the endpoint map fills the full `C` family through
selected-entry residual data, so the image is a selected-entry chart-image
slice of the determinant chart rather than a full-dimensional determinant-chart
region.

## Nonclaims

No determinant-chart Haar domination is proved, and unrestricted full
determinant-chart Haar domination is not expected for this source without
enlarging the source domain.  The domination target is the actual endpoint
image measure, not Haar.  No Jacobian formula for `Y` is proved.  No exact Haar
transport, raw-Haar pushforward, Haar normalization, original source-prior
transport, source-image coverage, source-rank coverage, normal crossings, pole
order, or RLCT extraction is claimed.
