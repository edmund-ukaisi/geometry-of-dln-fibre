# Statement Card - A2 product-step F3 ambient derivative

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepDerivative.lean`

## Claim

Lean now proves the Frechet derivative of the p. 13 ambient tuple coordinate
component

```text
F3 = F3old - D A3 (C1 A1)^{-1}
```

and identifies it with the already-landed formal Jacobian component
`productReductionStepFormalJacobian_dF3`.

## Lean Names

```text
hasFDerivAt_productReductionStepTopologyTupleToChart_F3
```

The proof reuses:

```text
hasFDerivAt_matrix_inv_of_isUnit_det
hasFDerivAt_productReductionStepTopologyTupleToChart_Ctop
matrixMulContinuousLinearMap
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- `[Finite pi] [Finite nu]` for finite-dimensional continuous-linear coercions;
- raw base point `x`;
- determinant-chart hypotheses `IsUnit x.C1.det` and `IsUnit x.A1.det`.

The determinant hypotheses are used to obtain invertibility of
`Ctop = x.C1 * x.A1`, so the inverse derivative applies to `Ctop^{-1}`.

## Not Proved

This is not the full ambient derivative of the p. 13 coordinate map.  It does
not prove the `C` component derivative, analytic determinant unitness,
source-measure pushforward, density transport, change of variables for
integrals, normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
```

Verified on 2026-06-26 with the focused module build passing.
