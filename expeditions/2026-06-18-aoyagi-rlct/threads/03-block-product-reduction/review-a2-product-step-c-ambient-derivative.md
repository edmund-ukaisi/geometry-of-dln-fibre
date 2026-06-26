# Review - A2 product-step C ambient derivative

Date: 2026-06-26.

Reviewers: controller; xhigh read-only Lean scout `Cicero`.

## Verdict

Pass for the `C` component derivative checkpoint.  The theorem proves exactly
the analytic derivative of the coordinate `A4 - A3*A1^{-1}*A2` and does not
claim the full p. 13 analytic Jacobian or any measure transport.

## Mathematical Check

Set

```text
L = A3 A1^{-1}.
```

The determinant hypothesis on `A1` gives

```text
d(A1^{-1}) = - A1^{-1} dA1 A1^{-1}.
```

Thus

```text
d(A3 A1^{-1} A2)
  = dA3 A1^{-1} A2
    - L dA1 A1^{-1} A2
    + L dA2.
```

Since `C = A4 - A3 A1^{-1} A2`, the derivative is

```text
dC = dA4
     - dA3 A1^{-1} A2
     + L dA1 A1^{-1} A2
     - L dA2.
```

This matches `productReductionStepFormalJacobian_dC`; the `dA1` term has a
positive sign because the inverse derivative is negative and the whole tail is
subtracted.

## Lean/API Check

The proof groups the tail as `(A3*A1^{-1})*A2`.  This gives a derivative
expression matching the formal component definition, whose local abbreviation
`leftA3` is `x.A3*x.A1^{-1}`.  It uses the matrix inverse derivative for
`A1^{-1}` and `matrixMulContinuousLinearMap` for the two product-rule layers.
The final continuous-linear-map equality is discharged by extensionality,
entrywise simplification, and matrix associativity.

## Scope Check

All individual ambient coordinate derivatives are now landed: `Ctop`, `F2`,
`F3`, and `C`, with passive coordinates `D`, `A1`, and `A3` handled by
projection derivatives.  The full ambient tuple derivative, analytic
determinant comparison, source-measure pushforward, normal crossings, pole
order, and RLCT remain open.
