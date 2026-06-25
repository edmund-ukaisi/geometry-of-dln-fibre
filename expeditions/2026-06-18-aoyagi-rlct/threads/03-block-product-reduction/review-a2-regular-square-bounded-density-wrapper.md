# Review - A2 regular-square bounded-density wrapper

Date: 2026-06-25.

Reviewer: xhigh independent reviewer Mendel the 4th.

## Verdict

No blocking issues found.

## Checks

- The exponent is coherent: `s = t + dim(E)/2`.
- The domination constant is correct: `c^(-s) * C`.
- The proof uses the needed supported-ball hypotheses:
  `c*(a+||u||^2) <= loss`, `0 <= density`, and `density <= C`.
- The theorem names match the content: a coordinate-square-sum theorem and a
  residual-block specialization.
- The notes do not claim Aoyagi's p.13 chart construction, Jacobian/prior
  transport, threshold equality, normal crossings, pole order, or RLCT.

## Nonblocking Suggestions Addressed

- The older theorem-ledger target row was reconciled: finite-side supplied
  wrappers are now Lean, while the full p.13 chart/density theorem remains
  open.
- The reproduction note and statement card now say that the regular ball is
  only the fiber `E` ball; any base or chart restriction must be encoded in
  the base measure.
