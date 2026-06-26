# Statement Card - A2 product-step raw-order ambient derivative

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepDerivative.lean`

## Claim

Lean now proves that composing the ambient tuple-level p. 13 coordinate map
with the chart-to-raw tangent reorder has Frechet derivative equal to
`productReductionStepFormalJacobianRawOrder x`.

## Lean Names

```text
hasFDerivAt_productReductionStepTopologyTupleToChart_rawOrder
```

The theorem uses:

```text
hasFDerivAt_productReductionStepTopologyTupleToChart
productReductionStepChartTangentRawOrderEquiv
productReductionStepFormalJacobianRawOrder
```

The existing determinant-unit certificate for the derivative target is:

```text
productReductionStepFormalJacobianRawOrder_det_isUnit
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- `[Finite pi] [Finite nu]`;
- raw base point `x`;
- determinant-chart hypotheses `IsUnit x.C1.det` and `IsUnit x.A1.det`.

## Not Proved

This is still an ambient Frechet derivative theorem.  It does not prove the
subtype chart derivative, source-measure pushforward, density transport,
change of variables for integrals, normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
```

Verified on 2026-06-26 with the focused module build passing.
