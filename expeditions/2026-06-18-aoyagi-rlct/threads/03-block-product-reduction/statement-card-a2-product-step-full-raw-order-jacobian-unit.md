# Statement Card - A2 product-step full raw-order Jacobian unit

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`

## Claim

After reordering the chart-output tangent coordinates into raw-shaped order,
the full p. 13 formal tangent map is a linear automorphism whose finite
`LinearMap.det` is a unit on the determinant chart.

## Lean Names

```text
productReductionStepFormalJacobianRawOrder
productReductionStepFormalJacobianRawOrder_apply
productReductionStepFormalJacobianRawOrderEquiv
productReductionStepFormalJacobianRawOrderEquiv_apply
productReductionStepFormalJacobianRawOrder_det_isUnit
```

## Inputs

- `[CommRing K]`;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- `[Finite pi] [Finite nu]` for the determinant theorem;
- raw base point `x`;
- determinant-chart hypotheses `IsUnit x.C1.det` and `IsUnit x.A1.det`.

No determinant hypothesis on `D`, `A3`, `F3`, or `C` is present.

## Not Proved

This is not an analytic Jacobian theorem.  It does not prove
`HasFDerivAt`, source-measure pushforward, density transport, exact
change-of-variables for integrals, chart coverage, normal crossings, pole
order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
```

Verified on 2026-06-26 with the focused module build passing.
