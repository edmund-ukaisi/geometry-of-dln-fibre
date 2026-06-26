# Statement Card - A2 product-step raw-order injectivity on determinant chart

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepDerivative.lean`

## Claim

Lean proves that the exact raw-order p. 13 ambient tuple map used in the
derivative theorem is injective on the raw determinant-chart set.

## Lean Names

```text
ProductReductionStepRawCoordinates.topologyTuple_injective
ProductReductionStepChartCoordinates.topologyTuple_injective
productReductionStepRawCoordinatesOfTopologyTuple
productReductionStepTopologyTupleToChart_ofTopologyTuple
injOn_productReductionStepTopologyTupleToChart_rawOrder_detChart
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- `[Finite pi] [Finite nu]`;
- membership in the raw determinant-chart set.

## Not Proved

This is not a measure pushforward theorem, not a density transport theorem,
not an image-identification theorem, not a normal-crossing certificate, and
not an RLCT or pole-order theorem.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
```

Verified on 2026-06-26 with the focused module build passing.

