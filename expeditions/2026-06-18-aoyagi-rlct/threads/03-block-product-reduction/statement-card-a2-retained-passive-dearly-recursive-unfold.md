# Statement Card - A2 retained-passive dEarly recursive unfold

Status: reproduced by controller; Lean proved; focused and full builds passed;
`scripts/sorries`, `git diff --check`, and axiom audit passed; xhigh
math/Lean/hardener scout checks and implementation review passed.

## Claim

For a retained-passive tuple `z` in the determinant chart and tangent `v`, the
Frechet derivative of the lower-left product-tail sum used as `Early` in the
positive-tail `F3` bridge unfolds recursively by the product rule.

For `p : Fin (M + 1)`, set

```text
E_p(y) = retainedPassiveLowerLeftProductTailSum A_y B_y C_y p.val,
D_p(y) = residualFactorProduct C_y (Fin.last (M+1)) p.succ,
G_p(y) = retainedPassiveA3WithoutLast(data_y.A3seed)(p),
P_p(y) = residualFactorProduct A_y (Fin.last (M+1)) p.castSucc.
```

Then

```text
dE_p =
  -(dD_p * G_p * P_p^-1
      + D_p * dG_p * P_p^-1
      + D_p * G_p * d(P_p^-1))
    + dE_{p+1}.
```

On the determinant chart,

```text
d(P_p^-1) = -P_p^-1 * dP_p * P_p^-1.
```

## Lean Target

Likely Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

Lean name:

```text
fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply
```

The theorem keeps the derivative of the current summand explicit.  A later
companion may expand the inverse derivative.

## Assumed

The theorem should assume:

```text
z in topologyTupleDetChartSet.
p : Fin (M + 1).
```

The determinant-chart hypothesis supplies invertibility of the solved top
product `P_p`.

## Dependencies

- `retainedPassiveLowerLeftProductTailSum_castSucc`;
- `differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet`;
- `differentiableAt_residualFactorProduct_C`;
- `differentiableAt_retainedPassiveA3WithoutLast`;
- `differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet`;
- `residualFactorProduct_solvedA1_det_isUnit_of_detChart`;
- `hasFDerivAt_matrix_inv_of_isUnit_det`;
- matrix multiplication product-rule API via `matrixMulContinuousLinearMap`.

## Review

Xhigh scouts `Tesla`, `Beauvoir`, and `Linnaeus` passed the recurrence scope.
Xhigh implementation reviewer `Faraday` passed the Lean theorem.  Review
artifact:

```text
review-a2-retained-passive-dearly-recursive-unfold.md
```

## Cited

None.

## Deferred

Source- or target-staging of the derivative pieces `dD_p`, `dG_p`, and `dP_p`;
iteration of the recurrence into a full `dEarly` target expression; full
positive-tail `F3` target staging; whole-tuple target-side normalization;
determinant-one target-side `LinearEquiv`; actual derivative determinant
equality; measure transport; normal crossings; pole order; RLCT.

## Kill Conditions

- The theorem must use `retainedPassiveA3WithoutLast`, whose terminal value is
  zero, not the solved terminal lower-left block.
- The theorem must preserve the order `D_p * G_p * P_p^-1` and
  `P_p^-1 * dP_p * P_p^-1`.
- The theorem must not claim target staging for `dEarly`.
- The theorem must not claim determinant equality, determinant-one target
  shear, measure transport, normal crossings, pole order, or RLCT.
