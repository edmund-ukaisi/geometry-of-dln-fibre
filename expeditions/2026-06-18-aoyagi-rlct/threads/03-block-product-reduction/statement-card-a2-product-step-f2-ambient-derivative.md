# Statement Card - A2 product-step F2 ambient derivative

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepDerivative.lean`

## Claim

Lean now proves the Frechet derivative of the p. 13 ambient tuple coordinate
component

```text
F2 = - A1^{-1} A2
```

and identifies it with the already-landed formal Jacobian component
`productReductionStepFormalJacobian_dF2`.

## Lean Names

```text
matrixMulContinuousLinearMap
matrixMulContinuousLinearMap_apply
hasFDerivAt_productReductionStepTopologyTupleToChart_F2
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- `[Finite pi] [Finite nu]` for finite-dimensional continuous-linear coercions;
- raw base point `x`;
- determinant-chart hypothesis `IsUnit x.A1.det`.

No determinant hypothesis on `C1`, `D`, `A2`, `A3`, `A4`, or the old `F3` is
used for this component.

## Not Proved

This is not the full ambient derivative of the p. 13 coordinate map.  It does
not prove the `F3` or `C` component derivatives, analytic determinant
unitness, source-measure pushforward, density transport, change of variables
for integrals, normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
```

Verified on 2026-06-26 with the focused module build passing.
