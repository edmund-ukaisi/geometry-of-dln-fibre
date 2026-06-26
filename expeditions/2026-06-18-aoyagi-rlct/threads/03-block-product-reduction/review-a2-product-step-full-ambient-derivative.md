# Review - A2 product-step full ambient derivative

Date: 2026-06-26.

Reviewers: controller.

## Verdict

Pass for the full ambient derivative checkpoint.  The theorem proves the
Frechet derivative of the tuple-level p. 13 coordinate formula and identifies
it with the bundled formal Jacobian.  It does not claim determinant
nonvanishing, change of variables, density transport, or RLCT.

## Mathematical Check

The chart tangent order is

```text
(dCtop,dD,dA1,dA3,dF2,dF3,dC).
```

The landed component theorems provide exactly these components:

```text
dCtop = dC1 A1 + C1 dA1
dF2   = A1^{-1} dA1 A1^{-1} A2 - A1^{-1} dA2
dF3   = dF3old
         - dD A3 Ctop^{-1}
         - D dA3 Ctop^{-1}
         + D A3 Ctop^{-1} dCtop Ctop^{-1}
dC    = dA4
         - dA3 A1^{-1} A2
         + A3 A1^{-1} dA1 A1^{-1} A2
         - A3 A1^{-1} dA2.
```

The remaining components `D`, `A1`, and `A3` are coordinate projections.  The
full derivative is therefore the product of these seven component derivatives,
which is exactly `productReductionStepFormalJacobian`.

## Lean/API Check

The proof uses `HasFDerivAt.prodMk` recursively.  It installs local
`Fintype` instances for `pi` and `nu` from the finite hypotheses, matching the
component theorem requirements.  The final `simpa` unfolds
`productReductionStepFormalJacobian` and the passive projection continuous
linear maps, so the derivative target is the bundled formal Jacobian rather
than an unbundled tuple expression.

## Scope Check

The next analytic boundary is not another component derivative.  The remaining
work is to connect this derivative to the determinant-unit formal Jacobian
certificate in the correct raw order, then to source-measure/density transport
or the normal-crossing chart certificate.  No such measure-theoretic or RLCT
claim follows from this theorem alone.
