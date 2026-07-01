# Statement Card - A2 Case 2 endpoint-reference raw-order/source-chart handoff

## Claim

On the local determinant/punctured-sector shrink, the named endpoint reference
image, raw-order reference image, and source-chart reference commute with the
actual maps:

```text
Measure.map Phi endpointReferenceImage
  =
rawOrderReferenceImage

Measure.map rawChart rawOrderReferenceImage
  =
Measure.map sourceChart (referenceSource.restrict V).
```

Here:

```text
endpointReferenceImage =
  case2PassiveThetaEndpointReferenceImageMeasure ... Rres V

rawOrderReferenceImage =
  case2PassiveThetaRawOrderReferenceImageMeasure ... Rres V

rawMap(theta) = Phi (Y theta).
```

Expected public Lean name:

```text
exists_open_subset_case2PassiveThetaEndpointReferenceImage_rawOrder_sourceChart_handoff
```

## Inputs Used

- concrete reference source
  `case2PassiveThetaReferenceSourceMeasure`;
- endpoint reference image
  `case2PassiveThetaEndpointReferenceImageMeasure`;
- raw-order reference image
  `case2PassiveThetaRawOrderReferenceImageMeasure`;
- local raw-order/source-chart package
  `exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext`;
- continuity of `Y`;
- continuity of `topologyTupleEdgeRawOrder` on the determinant-chart subtype.

## Nonclaims

No Haar identification, original-volume/source-prior transport, source-image
coverage, source-rank coverage, normal crossings, pole order, or RLCT
extraction is claimed.
