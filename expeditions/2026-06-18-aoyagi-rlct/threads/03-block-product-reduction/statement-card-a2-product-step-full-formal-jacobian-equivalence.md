# Statement Card - A2 product-step full formal Jacobian equivalence

## Lean File

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`

## Claim

At a raw base point whose `C1` and `A1` determinants are units, the full p. 13
formal tangent map from raw tangent coordinates to chart tangent coordinates is
a `LinearEquiv` with inverse given by the raw-derived chart-base inverse
formula.

## Lean Names

```text
productReductionStepFormalJacobianInverseFormula_formula_chartBase
productReductionStepFormalJacobianFormula_inverseFormula_chartBase
productReductionStepFormalJacobianEquiv
productReductionStepFormalJacobianEquiv_apply
productReductionStepFormalJacobianEquiv_symm_apply
```

## Inputs

- `[CommRing K]`;
- `[Fintype rho] [DecidableEq rho]`;
- `[Fintype mu]`;
- raw base point `x`;
- determinant-chart hypotheses `IsUnit x.C1.det` and `IsUnit x.A1.det`.

No determinant-unit theorem is stated in this slice, so no `[Finite pi]` or
`[Finite nu]` hypotheses are needed here.

## Not Proved

The full determinant-unit theorem is still open.  It should be stated only for
the raw-order endomorphism obtained by composing the raw-to-chart map with
`productReductionStepChartTangentRawOrderEquiv`.

No analytic derivative, source-measure pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT is proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
```

Verified on 2026-06-26 with the focused module build passing.
