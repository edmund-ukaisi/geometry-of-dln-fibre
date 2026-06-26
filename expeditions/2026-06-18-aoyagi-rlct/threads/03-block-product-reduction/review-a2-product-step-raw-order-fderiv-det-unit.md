# Review - A2 product-step raw-order fderiv determinant unit

Date: 2026-06-26.

Reviewers: controller.

## Verdict

Pass for the actual ambient `fderiv` determinant bridge.  The theorem is a
non-vacuous consequence of the landed raw-order `HasFDerivAt` statement and
the landed formal determinant-unit theorem.

## Mathematical Check

The raw-order derivative theorem identifies the Frechet derivative candidate
as the continuous-linear version of

```text
productReductionStepFormalJacobianRawOrder x.
```

`HasFDerivAt.fderiv` then identifies the actual `fderiv` with that candidate.
Taking `ContinuousLinearMap.det` reduces to the determinant of the underlying
formal `LinearMap`, so the result is exactly
`productReductionStepFormalJacobianRawOrder_det_isUnit`.

## Scope Check

The statement is intentionally ambient and determinant-only.  It does not
move to determinant-chart subtypes, does not state a local diffeomorphism or
Jacobian change-of-variables theorem, and does not assert source-measure
pushforward, density transport, normal crossings, pole order, or RLCT.
