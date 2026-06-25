# Review - A2 p.13 regular-coordinate bounded-density adapter

Date: 2026-06-25.

Reviewer: xhigh independent reviewer Pasteur the 4th.

## Verdict

No blocking issues found.

## Checks

- Focused module build passed:
  `lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability`.
- The regular-coordinate index is the three-block p.13 index and its packaged
  cardinality is correctly reused as
  `aoyagiTheorem2RegularVariableCount N H r`.
- The exponent shift is coherent:
  `t + finrank_R(EuclideanSpace R rho)/2` is rewritten to
  `t + aoyagiTheorem2RegularVariableCount N H r / 2`.
- The `R>0` hypothesis is appropriate for the source-facing local-ball
  adapter, even though the generic finite-side theorem is true for an empty
  ball.
- The theorem keeps product-chart, loss-comparison, residual-base, and
  density/Jacobian hypotheses supplied.

## Nonblocking Suggestions Addressed

- The reproduction note now distinguishes Aoyagi p.13's displayed lower-right
  literal block `prod_s C^(s) - F3 F2` from the cleaned residual block
  `prod_s C^(s)` consumed after finite square-sum comparison.

## Residual Risk

The statement-card pseudo-integral uses `1_{ball}` notation for readability;
Lean implements this as `Set.indicator` inside `ENNReal.ofReal`.  This is a
notation difference, not a mathematical issue.
