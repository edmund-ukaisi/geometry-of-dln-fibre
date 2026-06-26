# Statement Card - A2 p.13 left-step raw tuple measurability

## Lean Files

- `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`
- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`

## Claim

Lean proves that the p.13 explicit raw preimage tuple and the actual
constructed left-step raw tuple are measurable whenever the fixed-base edge
matrix family consumed by the suffix recursion is measurable.  Consequently,
the conditional p.13 raw pushforward consumer no longer needs a separate raw
tuple a.e.-measurability input in the fixed-base edge-matrix setting.

The raw-Haar pushforward remains an explicit hypothesis.

## Lean Names

```text
measurable_chartLocalSuffixState_residualProduct_real
measurable_chartLocalSuffixState_residualBlock_real
measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
aemeasurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
measurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
aemeasurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix
```

## Proved

- The suffix-recursion residual product and residual block are measurable
  functions of a measurable real edge-matrix family.
- The explicit p.13 raw tuple
  `(I,Dtail,F3,Ctop,-Ctop*F2,0,C0)` is measurable from fixed-base edge-matrix
  measurability and Euclidean regular-coordinate measurability.
- The actual constructed p.13 left-step raw tuple is measurable by equality
  with the explicit raw tuple.
- The conditional inverse-Jacobian measure consumer can derive the raw tuple
  a.e.-measurability input from fixed-base edge-matrix measurability.

## Assumed

- Finite-dimensional real endpoint data and the fixed complement `U0`.
- Measurability of the fixed-base edge-matrix family
  `paperEndpointFixedBaseEdgeMatrixOfReverseEdges ... CedgeBase`.
- For the final measure consumer only: an additive Haar measure `m`, a source
  measure `eta`, and the explicit raw pushforward hypothesis
  `Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta =
  m.restrict rawDetChart`.

## Cited

None.

## Deferred

Raw `Measurable CedgeBase` for arbitrary continuous-linear-map spaces, the
actual p.13 source-chart/pushforward construction, original DLN source/prior
transport, signed-box density identification, product-measure pushforward,
regular-suspension certification, normal crossings, pole order, and RLCT
extraction.

## Verification

Focused checks passed on 2026-06-26:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ChartTopology
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

The second check still reports the existing flexible tactic warnings around
`ProductReductionStepRegularDensity.lean:631`.

Review:

```text
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/review-a2-p13-left-step-raw-tuple-measurability.md
```

xhigh review passed on 2026-06-26 with no blocking findings.
