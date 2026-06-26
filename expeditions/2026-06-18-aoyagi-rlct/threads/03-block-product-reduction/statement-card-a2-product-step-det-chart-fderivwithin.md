# Statement Card - A2 product-step determinant-chart `fderivWithin`

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepDerivative.lean`

## Claim

Lean proves that the raw one-step determinant chart is open in the ambient
tuple coordinate space, that the raw-order p. 13 coordinate map has the landed
formal derivative within this open domain, and that the determinant of this
`fderivWithin` is a unit at determinant-chart points.

## Lean Names

```text
isOpen_productReductionStepRawTopologyTuple_detChart
hasFDerivWithinAt_productReductionStepTopologyTupleToChart_rawOrder_detChart
fderivWithin_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- `[Finite pi] [Finite nu]` for the derivative/determinant statements;
- raw base point `x`;
- determinant-chart hypotheses `IsUnit x.C1.det` and `IsUnit x.A1.det`.

## Not Proved

This is not a derivative theorem on the determinant-chart subtype. It is not a
source-measure pushforward, density transport theorem, change-of-variables
theorem for integrals, normal-crossing certificate, pole-order theorem, or
RLCT theorem.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
```

Verified on 2026-06-26 with the focused module build passing.
