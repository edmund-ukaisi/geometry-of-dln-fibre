# Statement Card - A2 product-step full ambient derivative

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepDerivative.lean`

## Claim

Lean now proves that the ambient tuple-level p. 13 product-step coordinate map

```text
productReductionStepTopologyTupleToChart
```

has Frechet derivative equal to the bundled formal p. 13 Jacobian
`productReductionStepFormalJacobian x`.

## Lean Names

```text
hasFDerivAt_productReductionStepTopologyTupleToChart
```

The proof assembles:

```text
hasFDerivAt_productReductionStepTopologyTupleToChart_Ctop
hasFDerivAt_productReductionStepTopologyTupleToChart_F2
hasFDerivAt_productReductionStepTopologyTupleToChart_F3
hasFDerivAt_productReductionStepTopologyTupleToChart_C
```

and the passive projection derivatives for `D`, `A1`, and `A3`.

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- `[Finite pi] [Finite nu]` for finite-dimensional continuous-linear coercions;
- raw base point `x`;
- determinant-chart hypotheses `IsUnit x.C1.det` and `IsUnit x.A1.det`.

## Not Proved

This is an ambient Frechet derivative theorem only.  It does not prove
analytic determinant unitness, source-measure pushforward, density transport,
change of variables for integrals, normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
```

Verified on 2026-06-26 with the focused module build passing.
