# Statement Card - A2 product-step weighted Haar change of variables

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean`

## Claim

Lean proves the Mathlib Jacobian change-of-variables adapter for the raw-order
p. 13 product-step coordinate map on the raw determinant chart.

For any additive Haar measure `m` on the raw tuple space and any
null-measurable raw determinant-chart set, the raw-order coordinate map pushes
forward the source measure weighted by the absolute determinant of its
continuous-linear derivative to `m` restricted to the image.

## Lean Names

```text
ProductReductionStepRawTopologyTuple
productReductionStepRawDetChartSet
isOpen_productReductionStepRawDetChartSet
nullMeasurableSet_productReductionStepRawDetChartSet
productReductionStepTopologyTupleToChartRawOrder
productReductionStepRawOrderJacobianCLM
productReductionStepRawOrderJacobianAbsDet
map_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart_withDensity_abs_det
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype pi] [Fintype mu] [Fintype nu]`;
- a measurable/Borel-space structure on the raw tuple space;
- an additive Haar measure `m`;
- `NullMeasurableSet (productReductionStepRawDetChartSet rho pi mu nu) m`.

## Not Proved

This is not an unweighted pushforward theorem, not original DLN source/prior
measure transport, not an image-identification theorem for the full target
determinant chart, not source coverage, not a normal-crossing certificate, and
not an RLCT or pole-order theorem.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
```

Full check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre
```

Verified on 2026-06-26 with both builds passing.
