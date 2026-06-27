# Statement Card - A2 retained-passive dEarly dPcast solvedA1 product rule

Status: reproduced by controller; Lean target selected.

## Claim

For the solved-`A1` residual suffix product

```text
Pcast(y) = residualFactorProduct solvedA1_y final p.castSucc,
Psucc(y) = residualFactorProduct solvedA1_y final p.succ,
```

the residual-factor unfold gives `Pcast(y) = Psucc(y) * solvedA1_y(p)`.
Therefore, at a tuple determinant-chart point `z`,

```text
dPcast_z(v)
  = dPsucc_z(v) * solvedA1_z(p)
    + Psucc(z) * d(solvedA1 p)_z(v).
```

The second summand deliberately leaves
`d(solvedA1 p)_z(v)` explicit.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Planned Lean name:

```text
fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply
```

## Dependencies

- `residualFactorProduct_castSucc`;
- `differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet`;
- `differentiableAt_solvedA1_of_mem_topologyTupleDetChartSet`;
- `matrixMulContinuousLinearMap` and its bilinear derivative API.

## Cited

None.

## Deferred

Derivative formula for `solvedA1 0`; complete source-staging of `dPcast`;
substitution into the `dEarly` recurrence; closed finite-sum formula; target
staging; determinant theorem; measure theorem; normal crossings; pole order;
RLCT.

## Kill Conditions

- Do not replace `(fderiv solvedA1 p)` by a passive source tangent in this
  theorem.
- Do not import downstream Jacobian recovery theorems into the derivative file.
- Preserve the factor order
  `dPsucc * solvedA1_z(p) + Psucc(z) * d(solvedA1 p)`.
- Do not claim determinant equality, measure transport, normal crossings, pole
  order, or RLCT.
