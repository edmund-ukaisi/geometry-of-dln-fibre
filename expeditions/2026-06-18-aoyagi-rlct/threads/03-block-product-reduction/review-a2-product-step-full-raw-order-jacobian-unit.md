# Review - A2 product-step full raw-order Jacobian unit

Date: 2026-06-26.

Reviewers: controller plus xhigh pen-and-paper reviewer `Hume`.

## Verdict

Pass for the finite determinant-unit checkpoint.  The theorem correctly takes
the determinant only after composing the native raw-to-chart formal tangent
map with the chart-output raw-order permutation.

## Mathematical Check

Let

```text
Raw   = ProductReductionStepRawTangent,
Chart = ProductReductionStepChartTangent.
```

The previous checkpoint gives

```text
J : Raw ~= Chart
```

in native chart order `(Ctop,D,A1,A3,F2,F3,C)`.  The reorder equivalence gives

```text
P : Chart ~= Raw
```

by sending the native chart tuple to raw-shaped order
`(Ctop,D,F3,A1,F2,A3,C)`.  Hence `J.trans P : Raw ~= Raw` is a linear
automorphism.  Its determinant is a unit by the general determinant theorem
for linear equivalences.

No determinant expansion, permutation sign, or exact exponent is needed for
unitness.  The reorder is type-correct because the paired slots have matching
matrix shapes: `Ctop/C1`, `F3/F3old`, `F2/A2`, `C/A4`, and unchanged
`D,A1,A3`.

## Lean/API Check

The landed endomorphism is

```text
productReductionStepFormalJacobianRawOrder
```

defined as the composition of
`productReductionStepFormalJacobian` with
`productReductionStepChartTangentRawOrderEquiv.toLinearMap`.  The automorphism
witness is the corresponding transposed equivalence

```text
productReductionStepFormalJacobianRawOrderEquiv
```

and the determinant theorem is exactly

```text
productReductionStepFormalJacobianRawOrder_det_isUnit
```

using `LinearEquiv.isUnit_det'`.  The theorem locally installs `Fintype`
instances for `pi` and `nu` from `[Finite pi] [Finite nu]`, matching the
earlier determinant-unit API.

## Scope Check

This theorem is a finite formal determinant-unit certificate.  It is not an
analytic derivative theorem, local analytic chart theorem, source-measure
pushforward, density/Jacobian transport, exact determinant formula, normal
crossing result, pole-order result, or RLCT result.

The raw-shaped codomain is semantically chart output in raw tuple slots.  Any
comparison with a printed ordered Jacobian matrix would require a separate
order/sign audit.
