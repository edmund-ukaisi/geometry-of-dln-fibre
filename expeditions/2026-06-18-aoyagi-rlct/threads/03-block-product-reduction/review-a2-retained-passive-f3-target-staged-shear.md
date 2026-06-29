# Review - A2 Retained-Passive F3 Target-Staged Shear

Date: 2026-06-29.

Reviewer: xhigh `Bernoulli`.

## Verdict

No findings.

## Checks

- Positive-tail indexing is consistent: the theorem uses
  `κ' : Fin ((M+1)+2) -> Type*`, invokes the existing `F3` shear with
  `M := M+1`, and rewrites `dEarly` using the target-staged theorem at
  `M` and `m = 0`.
- Product order and signs match the terminal `F3` product-rule cancellation:
  `raw F3 = -((F3 - Early) * LastTop)`, the correction is
  `-dEarly * LastTop + (F3 - Early) * dLastTop`, and the right side is
  `dF3 * (-LastTop)`.
- The notes frame the theorem as a positive-tail substitution wrapper and do
  not claim determinant equality, formal-Jacobian equality, measure transport,
  normal crossings, pole order, or RLCT.
- The theorem is non-vacuous as a Lean-facing wrapper because it replaces the
  analytic `fderiv Earlyfun` term with the target-staged recurrence term.

The reviewer stayed read-only and did not run Lean.
