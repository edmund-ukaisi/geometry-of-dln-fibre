# Statement card - A2 Case 2 passive theta raw-order two-stage source chart

Date: 2026-06-30.

## Statement

For the concrete full passive theta coordinate domain, there is an open
neighborhood `V` of any determinant-sector, nonzero-pivot base point such that
the endpoint topology tuple, after raw-order reindexing, gives the same p.13
source edge family as the direct passive-theta endpoint source chart:

```text
rawChart (rawMap theta) = sourceChart theta
```

for all `theta in V`.  Here

```text
rawMap theta =
  topologyTupleEdgeRawOrder
    (case2PassiveThetaEndpointTopologyTuple ... theta eNext e)
```

and `rawChart` is
`paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart`.

The same local theorem records:

```text
sourceReadback (edgeMatrix (sourceChart theta)) = retainedData theta
inverseReadout (sourceChart theta) = theta.yNext
```

pointwise on `V`, and for any theta-domain measure restricted to `V`,

```text
Measure.map (fun theta => rawChart (rawMap theta)) (sourceMeasure.restrict V)
  =
Measure.map sourceChart (sourceMeasure.restrict V)

Measure.map rawChart (Measure.map rawMap (sourceMeasure.restrict V))
  =
Measure.map sourceChart (sourceMeasure.restrict V)
```

under the target measurable/Borel hypotheses needed by the two-stage map.

## Lean Target

```text
exists_open_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

## Proof Idea

Unfold the concrete `Case2PassiveTheta` endpoint retained data, endpoint source
chart, endpoint topology tuple, and inverse readout.  The statement is then the
generic passive selected-entry theorem

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_twoStage_eq_sourceChart_inverseReadout_eq_snd
```

with the passive-field parameter specialized to the product of the five passive
theta fields.

## Nonclaims

No exact passive-sector Haar transport, determinant-chart Haar transport,
raw-order Haar transport, source-prior comparison, source-image equality,
source-rank coverage, passive-sector Jacobian formula, normal crossings, pole
order, or RLCT extraction is claimed.  The theorem does not prove endpoint
sector image measurability; that remains a later local inverse/image target.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-raw-order-two-stage-source-chart.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-raw-order-two-stage-source-chart.md
```
