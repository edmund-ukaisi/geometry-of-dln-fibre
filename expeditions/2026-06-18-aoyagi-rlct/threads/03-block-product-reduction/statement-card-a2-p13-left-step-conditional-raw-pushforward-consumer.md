# Statement Card - A2 p.13 left-step conditional raw pushforward consumer

## Lean Files

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`
- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`

## Claim

Lean proves a conditional measure consumer for the p. 13 left endpoint
product-step.  If the actual constructed left-step raw tuple pushes a source
measure to Haar measure restricted to the raw determinant chart, then the
explicit p. 13 raw-order target tuple has the chart-side inverse-Jacobian
density.

The source-side raw pushforward is an explicit hypothesis.

It should not be silently promoted to a theorem from p. 13 alone.  The p. 13
raw section fixes the full raw tuple coordinates `C1 = I` and `A3 = 0`, so in
nontrivial raw `C1` or `A3` directions its image is lower-dimensional inside
the raw determinant chart.  Lean records these section facts for both the
explicit raw preimage tuple and the actual constructed left-step raw tuple.

## Lean Names

```text
aemeasurable_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart
map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian
paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one
paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero
p13ProductCoordinateLeftStepRawTopologyTuple
p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one
p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
```

## Inputs

- An additive Haar measure `m` on the raw tuple space.
- A source measure `η`.
- A supplied pushforward identity saying the p. 13 raw preimage, or the
  actual constructed left-step raw tuple, maps `η` to `m.restrict rawDetChart`.
- A.e. determinant-unit condition for `Ctop(u)`.
- A.e. measurability of the raw source tuple.

Null-measurability of the raw determinant chart and a.e. measurability of the
raw-order map on `m.restrict rawDetChart` are derived internally from openness
of the chart and continuity on the chart.

## Method

The generic lemma composes a supplied source-side raw pushforward with

```text
map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian.
```

The p. 13 raw-preimage theorem rewrites the raw-order product-step image of

```text
(I,Dtail,F3,Ctop,-Ctop*F2,0,C0)
```

to

```text
(Ctop,Dtail,F3,Ctop,F2,0,C0)
```

almost everywhere using the supplied `det Ctop` hypothesis.

The actual-left-step theorem then uses
`p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple` to replace
the constructed left-step raw tuple by the explicit raw preimage tuple inside
the measure pushforward.

## Not Proved

This checkpoint does not prove the supplied raw pushforward hypothesis.  It
does not prove original DLN source/prior transport, source coverage, p. 13
source-chart construction from original coordinates, signed-box density
identification, product-measure pushforward, regular-suspension certification,
normal crossings, pole order, or RLCT.  In particular, the section facts
`C1 = I` and `A3 = 0` are guardrails against treating the p. 13 section as a
full raw determinant-chart Haar parametrisation.

## Verification

Focused checks:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

passed on 2026-06-26.

Review:

```text
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/review-a2-p13-left-step-conditional-raw-pushforward-consumer.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/review-a2-p13-left-step-raw-section-guardrail.md
```

xhigh review passed on 2026-06-26 with no findings.
Follow-up xhigh scout review recorded the raw-section guardrail on 2026-06-26.
