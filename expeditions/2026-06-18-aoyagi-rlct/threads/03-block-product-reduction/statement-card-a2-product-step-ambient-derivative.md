# Statement Card - A2 product-step ambient derivative

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepDerivative.lean`

## Claim

Lean now starts the analytic derivative layer for Aoyagi's p. 13 product-step
coordinate change.  It proves the Frechet derivative of real matrix inversion
on determinant-unit square matrices, defines the ambient tuple-level version
of the product-step coordinate map, relates that tuple map to the existing
record-level `toChart`/formal chart base, and proves the `Ctop = C1 * A1`
component derivative matches the corresponding component of the formal
Jacobian.

## Lean Names

```text
hasFDerivAt_matrix_inv_of_isUnit_det
productReductionStepTopologyTupleToChart
productReductionStepTopologyTupleToChart_topologyTuple
productReductionStepTopologyTupleToChart_topologyTuple_chartBase
hasFDerivAt_productReductionStepTopologyTupleToChart_Ctop
```

## Inputs

- real finite matrix coordinates;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]` for the product-step formulas;
- `[Finite pi] [Finite nu]` for the finite-dimensional continuous-linear
  coercion in the `Ctop` derivative theorem;
- determinant-unit hypothesis `IsUnit A.det` for the inverse derivative.

The `Ctop` component derivative does not use determinant-chart assumptions,
because it is just the product derivative for `C1 * A1`.

## Not Proved

This is not the full ambient derivative of all p. 13 chart coordinates.  It
does not prove the determinant of the analytic derivative, source-measure
pushforward, density transport, change of variables for integrals, source
coverage, exact-rank openness, normal crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
```

Verified on 2026-06-26 with the focused module build passing.
