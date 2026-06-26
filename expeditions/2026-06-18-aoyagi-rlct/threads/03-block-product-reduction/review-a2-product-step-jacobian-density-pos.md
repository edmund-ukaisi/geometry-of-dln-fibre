# Review - A2 product-step Jacobian density positivity

Date: 2026-06-26.

Verdict: accepted at the stated scope.

## Checks

- The determinant-unit theorem is obtained from the landed formal raw-order
  Jacobian determinant-unit theorem by unfolding the continuous-linear
  derivative family.
- Strict positivity uses only `abs_pos` and the nonzero determinant supplied
  by `IsUnit`.
- Eventual positivity uses only openness of the raw determinant chart and the
  pointwise positivity theorem.
- No continuity or upper-bound claim is hidden in the theorem names.

## Boundary

This is a local positivity bridge for the Jacobian density in the weighted
Haar theorem. It does not supply a bounded-density theorem, original
source/prior measure transport, source coverage, normal crossings, pole order,
or RLCT.
