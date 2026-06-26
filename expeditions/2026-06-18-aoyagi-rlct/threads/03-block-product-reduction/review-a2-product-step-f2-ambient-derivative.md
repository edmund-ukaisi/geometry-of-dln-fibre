# Review - A2 product-step F2 ambient derivative

Date: 2026-06-26.

Reviewers: controller; xhigh Lean proof scout `Parfit` was also launched for
the proof shape and had not reported a contradiction before the local proof
passed.

## Verdict

Pass for the `F2` component derivative checkpoint.  The theorem proves exactly
the first inverse-dependent analytic coordinate derivative and does not claim
the full p. 13 analytic Jacobian or any measure transport.

## Mathematical Check

For

```text
F2 = - A1^{-1} A2,
```

the determinant-unit hypothesis on `A1` gives

```text
d(A1^{-1})[dA1] = -A1^{-1} dA1 A1^{-1}.
```

The product rule then gives

```text
dF2 = A1^{-1} dA1 A1^{-1} A2 - A1^{-1} dA2,
```

which is exactly the formula encoded by
`productReductionStepFormalJacobian_dF2`.

## Lean/API Check

The theorem uses `hasFDerivAt_matrix_inv_of_isUnit_det` for the inverse
coordinate and the new `matrixMulContinuousLinearMap` helper for
heterogeneous matrix multiplication.  The final derivative equality is proved
by extensionality of continuous linear maps and entrywise simplification, so
the statement is tied directly to the formal component map rather than to an
unbundled expression.

## Scope Check

The remaining analytic derivative components are `F3` and `C`; both require
additional product-rule bookkeeping.  The full ambient tuple derivative, the
analytic determinant comparison, source-measure pushforward, normal crossings,
pole order, and RLCT remain open.
