# Review - A2 retained-passive fixed-base edge realisation

Reviewer: xhigh `Pasteur the 4th`.

## Verdict

Commit as-is.  No blocking findings.

## Checks

- The first Lean theorem is exactly the prescribed fixed-base matrix recovery
  theorem specialized to `data.edgeMatrix`.
- The readback theorem composes that matrix recovery with
  `sourceReadback_edgeMatrix_eq`.
- The determinant-chart hypothesis is absent from the fixed-base matrix
  realisation theorem and appears only in the readback theorem, matching the
  underlying inverse theorem.
- The older `hedge`-based bridge handles arbitrary `Cedge`; the new theorem is
  useful because it packages the important case where the fixed-base edge
  family is built directly from `data.edgeMatrix`.
- The local long-line linter suppressions are scoped and not a blocker.
- The reproduction and statement card state the nonclaims sharply enough.

## Nonclaims Rechecked

This slice is generic fixed-base edge realisation.  It is not Case 2 source
production, not a longer-suffix slicing theorem, not source-image coverage,
not source-measure or Jacobian transport, not original-loss comparison, not
normal crossings, not pole order, and not RLCT extraction.
