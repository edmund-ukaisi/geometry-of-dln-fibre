# Review - A2 Case 2 passive theta raw-order two-stage source chart

Date: 2026-06-30.

## Result

PASS.

## Reviewed Artifact

Lean theorem:

```text
exists_open_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-raw-order-two-stage-source-chart.md
```

## Source And Scope Review

Xhigh reviewer `Herschel` returned PASS.

The theorem is a legitimate Aoyagi-only source-moving adapter.  It specializes
the generic passive selected-entry raw-order bridge to concrete
`Case2PassiveTheta` maps:

```text
rawMap theta =
  topologyTupleEdgeRawOrder
    (case2PassiveThetaEndpointTopologyTuple ... theta eNext e)

sourceChart theta =
  case2PassiveThetaEndpointSourceChart ... theta

inverseReadout =
  case2PassiveThetaEndpointInverseReadout ...
```

It does not overclaim Haar/source-prior content.  The measure conclusion is
only equality of the composed and two-stage pushforwards through
`rawMap/rawChart` for an arbitrary theta-domain measure restricted to the
returned open `V`, under explicit target measurable/Borel instances.

Non-blocking caveat: the underlying generic construction obtains `V` by
intersecting determinant and nonzero-pivot neighborhoods, but this concrete
public theorem does not expose a separate `V ⊆ case2PassiveThetaPuncturedDetSector`
statement.  Bank it as a source-chart equality and raw-order two-stage
pushforward adapter, not as a reusable sector-containment theorem.

## Lean/API Review

Xhigh reviewer `Gibbs` returned PASS.

The statement shape matches the upstream two-stage selected-entry theorem:
local `V`, pointwise raw-chart/source-chart/readout facts, then one-stage and
two-stage `Measure.map` equalities.  The final proof is a definitional
specialization of

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_twoStage_eq_sourceChart_inverseReadout_eq_snd
```

with the passive-field parameter instantiated by the five passive theta fields.
Imports and measurable/Borel hypotheses are sufficient.

Non-blocking caveat: the theorem's `inverseReadout_eq_yNext` part is pointwise
on `V`; it does not additionally state

```text
Measure.map inverseReadout μ =
  Measure.map Case2PassiveTheta.yNext (sourceMeasure.restrict V).
```

Consumers needing that readout pushforward identity should use the earlier
source-chart theorem

```text
exists_open_measure_map_case2PassiveThetaEndpointSourceChart_puncturedSector_inverseReadout_eq_yNext
```

## Verification

Focused checks passed:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
```

The focused module build replayed pre-existing warning noise from
`ProductReductionStepRegularDensity.lean`; the touched file had no warning
after the heartbeat-budget comment was added.
