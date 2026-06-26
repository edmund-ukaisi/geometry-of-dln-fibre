# Statement Card - A2 product-step formal Jacobian A1 unit

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`

## Claim

Lean proves that the full p. 13 formal tangent map is a raw/chart
`LinearEquiv`, and that the chart-output raw-order formal Jacobian determinant
is a unit, under only `IsUnit A1.det`.  The older determinant-chart names
remain wrappers.

## Lean Names

```text
productReductionStepFormalJacobianInverseFormula_formula_chartBase_of_isUnit_A1
productReductionStepFormalJacobianFormula_inverseFormula_chartBase_of_isUnit_A1
productReductionStepFormalJacobianEquiv_of_isUnit_A1
productReductionStepFormalJacobianEquiv_of_isUnit_A1_apply
productReductionStepFormalJacobianEquiv_of_isUnit_A1_symm_apply
productReductionStepFormalJacobianRawOrderEquiv_of_isUnit_A1
productReductionStepFormalJacobianRawOrderEquiv_of_isUnit_A1_apply
productReductionStepFormalJacobianRawOrder_det_isUnit_of_isUnit_A1
```

Existing wrapper names:

```text
productReductionStepFormalJacobianInverseFormula_formula_chartBase
productReductionStepFormalJacobianFormula_inverseFormula_chartBase
productReductionStepFormalJacobianEquiv
productReductionStepFormalJacobianEquiv_apply
productReductionStepFormalJacobianEquiv_symm_apply
productReductionStepFormalJacobianRawOrderEquiv
productReductionStepFormalJacobianRawOrderEquiv_apply
productReductionStepFormalJacobianRawOrder_det_isUnit
```

## Inputs

- `[CommRing K]`;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- raw base point `x`;
- `IsUnit x.A1.det`;
- additionally `[Finite pi] [Finite nu]` for the determinant theorem.

The A1-only theorems do not require `IsUnit x.C1.det`.  The wrapper theorems
still accept `IsUnit x.C1.det` for determinant-chart compatibility.

## Not Proved

This is finite formal tangent algebra only.  It does not weaken analytic
derivative, determinant-chart, or measure hypotheses.  It does not prove
source coverage, source-measure transport, density/Jacobian identity, normal
crossings, pole order, or RLCT.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
```

Passed on 2026-06-26.
