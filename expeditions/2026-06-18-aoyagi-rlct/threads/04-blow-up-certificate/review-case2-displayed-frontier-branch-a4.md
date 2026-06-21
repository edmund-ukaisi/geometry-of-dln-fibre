# Review - A4 Case 2 displayed frontier branch

Review mode: xhigh independent scout/hardener plus controller integration.

## Verdict

Accepted at the narrow finite-frontier scope.

The Lean names do not claim chart coverage, chart production, transition
invariance, terminal source truth, normal crossings, pole order, or RLCT.  The
stopped branches are explicitly nonexclusive.

## Checks

- `Case2DisplayedStepBranch` is a supplied Prop-level branch witness, not an
  atlas or transition object.
- `case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont` uses the
  already-proved finite frontier theorem
  `case2_next_frontier_currentPrefixMin_or_nextWidth_eq_of_cont_of_not_next`.
- `Case2DisplayedSuppliedChartFamilyBoundary.frontierBranch` only projects
  `stage_pos` and `continuation` through the finite arithmetic theorem.
- The row-exhausted branch does not receive actual-width relabel certificates
  or original-row terminal data.

## Residual Risk

This result is only a small dispatcher for later work.  The branch-specific
product theorems remain separate supplied-boundary packages, and a future
combined theorem must preserve their different hypotheses and conclusions.
