# Review - A2 fixed-passive formal Jacobian determinant

Reviewer: xhigh read-only scout `Arendt the 4th`.

Status: passed; no blocking issues.

## Findings

No blocking issues were found.

The determinant formula is correct for the Lean-defined raw-to-chart map
`productStepFixedPassiveFormalJacobian`.  The non-shear diagonal blocks are
right multiplication by `A1` on `rho x rho` matrices and left multiplication
by `-A1^{-1}` on `rho x nu` matrices, giving

```text
A1.det ^ card rho * (-A1^{-1}).det ^ card nu
```

in raw-to-chart orientation.

The shear/diagonal factorization is faithful to the formal Jacobian
definition.  The `C` shear implements `dC = dA4 + A3*dF2`, and the `F3`
shear adds `D*A3*Ctop^{-1}*dCtop*Ctop^{-1}` to `dF3old`.  Both are
triangular additions with determinant one.

## Nonblocking Suggestions Addressed

The reproduction note now explicitly states that the real absolute-value
simplification

```text
|det J| = |det A1|^(|rho|) * |det A1|^(-|nu|)
```

is only on the determinant chart where `det A1` is nonzero.  It also states
that Lean intentionally proves the formal determinant identity without chart
invertibility hypotheses and does not simplify the reciprocal absolute-value
factor.

## Scope Check

No overclaiming was found around analytic `fderiv`, retained-passive total
determinant, source-prior transport, normal crossings, pole order, or RLCT.

The private product helpers are local determinant bookkeeping and do not leak
a public API.
