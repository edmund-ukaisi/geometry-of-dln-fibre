# Statement Card - A2 Case 2 passive-theta raw-order reference

## Claim

Lean names the concrete raw-order image of the Case 2 passive-theta reference
source:

```text
case2PassiveThetaRawOrderReferenceImageMeasure
  = Measure.map rawMap
      ((case2PassiveThetaReferenceSourceMeasure ...).restrict V),

rawMap(theta) =
  topologyTupleEdgeRawOrder
    (case2PassiveThetaEndpointTopologyTuple ... theta).
```

After the existing local determinant/punctured-sector shrink, this named
measure is supported on

```text
topologyTupleRawOrderSourceRecursiveDetChartSet.
```

The same local theorem also proves that passive-field scalar domination pushes
forward to domination by this named raw-order image measure.

Public Lean names:

```text
case2PassiveThetaRawOrderReferenceImageMeasure
exists_open_subset_case2PassiveThetaRawOrderReferenceImageMeasure_support_and_domination
```

## Inputs Used

- the concrete passive-theta reference source from
  `case2PassiveThetaReferenceSourceMeasure`;
- the local raw-order/source-chart package
  `exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext`;
- continuity of `case2PassiveThetaEndpointTopologyTuple`;
- continuity of `topologyTupleEdgeRawOrder` on the determinant-chart subtype;
- `passiveMeasure <= d • case2PassiveThetaPassiveFieldReferenceMeasure`.

## Output

There is an open local set `V`, contained in any prescribed open neighborhood
`G` of the determinant-sector and nonzero-pivot base point, such that:

```text
(case2PassiveThetaRawOrderReferenceImageMeasure ... V).restrict rawSourceSet
  =
case2PassiveThetaRawOrderReferenceImageMeasure ... V
```

and for every dominated passive-field measure,

```text
Measure.map rawMap ((passiveMeasure.prod weightedBox).restrict V)
  <=
d • case2PassiveThetaRawOrderReferenceImageMeasure ... V.
```

## Nonclaims

No unrestricted raw-Haar domination is proved.  No determinant-chart Haar
transport, endpoint-Haar comparison, exact raw-Haar pushforward, source-prior
comparison, source-image/source-rank coverage, normal crossings, pole order,
or RLCT extraction is claimed.
