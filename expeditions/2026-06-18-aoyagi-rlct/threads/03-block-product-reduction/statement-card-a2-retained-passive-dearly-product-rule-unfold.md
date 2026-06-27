# Statement Card - A2 retained-passive dEarly product-rule unfold

Status: reproduced by controller; Lean proved; focused and full builds passed;
`scripts/sorries`, `git diff --check`, and axiom audit passed; xhigh math and
Lean-terrain scout checks passed; implementation review passed.

## Claim

For a retained-passive tuple `z` in the determinant chart, tangent `v`, and
`p : Fin (M + 1)`, the derivative of the current summand in the lower-left
tail recurrence expands by the noncommutative product rule and the matrix
inverse derivative.

With

```text
D_p(y) = residualFactorProduct C_y (Fin.last (M+1)) p.succ,
G_p(y) = retainedPassiveA3WithoutLast(data_y.A3seed)(p),
P_p(y) = residualFactorProduct A_y (Fin.last (M+1)) p.castSucc,
E_next(y) = retainedPassiveLowerLeftProductTailSum ... (p.val + 1),
```

the theorem proves

```text
dE_p =
  -dD_p * G_p * P_p^-1
  -D_p * dG_p * P_p^-1
  +D_p * G_p * P_p^-1 * dP_p * P_p^-1
  +dE_next.
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Lean name:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply
```

## Inputs

The theorem assumes:

```text
z in topologyTupleDetChartSet.
p : Fin (M + 1).
```

The determinant-chart hypothesis supplies invertibility of `P_p` via
`residualFactorProduct_solvedA1_det_isUnit_of_detChart`.

## Dependencies

- `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply`;
- `differentiableAt_residualFactorProduct_C`;
- `differentiableAt_retainedPassiveA3WithoutLast`;
- `differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet`;
- `residualFactorProduct_solvedA1_det_isUnit_of_detChart`;
- `hasFDerivAt_matrix_inv_of_isUnit_det`;
- `matrixMulContinuousLinearMap`;
- `ContinuousLinearMap.hasFDerivAt_of_bilinear`;
- `fderiv_fun_neg`.

## Review

Xhigh scouts `Cicero` and `Euler` passed the math and Lean-terrain checks.
Xhigh implementation reviewer `Wegener` passed the Lean theorem.  Review
artifact:

```text
review-a2-retained-passive-dearly-product-rule-unfold.md
```

## Cited

None.

## Deferred

Source- or target-staging of `dD_p`, `dG_p`, and `dP_p`; iteration of the
recurrence into a closed `dEarly` expression; substitution into the
positive-tail `F3` bridge; whole-tuple target-side normalization; determinant
theorem; measure theorem; normal crossings; pole order; RLCT.

## Kill Conditions

- The theorem must keep the order `D * G * P^-1 * dP * P^-1`.
- The theorem must use `retainedPassiveA3WithoutLast`, not solved terminal
  `A3`, for the current lower-left factor.
- The theorem must not claim source staging or target staging.
- The theorem must not claim determinant equality, determinant-one target
  shear, measure transport, normal crossings, pole order, or RLCT.
