# Review - A2 product-step F3 ambient derivative

Date: 2026-06-26.

Reviewers: controller.

## Verdict

Pass for the `F3` component derivative checkpoint.  The theorem proves exactly
the analytic derivative of the coordinate
`F3old - D*A3*(C1*A1)^{-1}` and does not claim the full p. 13 analytic
Jacobian or any measure transport.

## Mathematical Check

Set

```text
Ctop = C1 A1,
dCtop = dC1 A1 + C1 dA1.
```

The determinant hypotheses on `C1` and `A1` imply that `Ctop` has determinant a
unit.  Hence

```text
d(Ctop^{-1}) = - Ctop^{-1} dCtop Ctop^{-1}.
```

For the tail product,

```text
d(D A3 Ctop^{-1})
  = dD A3 Ctop^{-1}
    + D dA3 Ctop^{-1}
    - D A3 Ctop^{-1} dCtop Ctop^{-1}.
```

Since `F3 = F3old - D A3 Ctop^{-1}`, the derivative is

```text
dF3 = dF3old
       - dD A3 Ctop^{-1}
       - D dA3 Ctop^{-1}
       + D A3 Ctop^{-1} dCtop Ctop^{-1}.
```

This matches `productReductionStepFormalJacobian_dF3`; the final sign is
positive because the inverse-derivative contribution is subtracted.

## Lean/API Check

The proof uses the landed `Ctop` component derivative, composes it with the
matrix inverse derivative at `Ctop`, and uses
`matrixMulContinuousLinearMap` for the two bilinear product-rule steps:
`D*A3` and `(D*A3)*Ctop^{-1}`.  The derivative equality is proved by
continuous-linear-map extensionality and entrywise simplification.  The only
nontrivial normalization is finite-sum distribution for the
`dCtop = dC1*A1 + C1*dA1` term.

## Scope Check

The remaining analytic derivative component is `C`.  The full ambient tuple
derivative, the analytic determinant comparison, source-measure pushforward,
normal crossings, pole order, and RLCT remain open.
