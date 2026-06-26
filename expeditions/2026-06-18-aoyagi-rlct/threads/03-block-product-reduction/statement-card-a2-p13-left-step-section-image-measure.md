# Statement Card - A2 p.13 left-step section-image measure

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`

## Claim

Lean proves the section-level measure identity for the p.13 left-step raw
tuple: if the actual p.13 left-step raw tuple lands in the raw determinant
chart almost everywhere, then the p.13 raw-order target measure is the
raw-order product-step image of the actual left-step raw image measure.

This does not identify the actual left-step raw image measure with full Haar
measure on the raw determinant chart.

## Lean Name

```text
map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
```

## Proved

```text
Measure.map paperEndpointFixedBaseP13RawOrderTuple eta =
  Measure.map productReductionStepTopologyTupleToChartRawOrder
    (Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta)
```

under fixed-base edge-matrix measurability and a.e. raw determinant-chart
membership of the actual left-step raw tuple.

## Assumed

- Finite-dimensional real endpoint data and fixed complement `U0`.
- Fixed-base edge-matrix measurability.
- A source measure `eta`.
- A.e. raw determinant-chart support for the actual p.13 left-step raw tuple.

## Cited

None.

## Deferred

Full raw-Haar pushforward, source/prior measure transport, p.13 source-chart
coverage, signed-box or product-coordinate density identification, residual
monomial bounds, normal crossings, pole order, and RLCT extraction.

## Verification

Focused check passed on 2026-06-26:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

The check still reports only the existing flexible tactic warning around
`ProductReductionStepRegularDensity.lean:631`.

Review:

```text
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/review-a2-p13-left-step-section-image-measure.md
```

xhigh landed-slice review passed on 2026-06-26 with no blocking findings.
