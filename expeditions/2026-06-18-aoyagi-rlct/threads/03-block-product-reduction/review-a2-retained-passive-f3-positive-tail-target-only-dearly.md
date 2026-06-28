# Review - A2 retained-passive F3 positive-tail target-only dEarly

Date: 2026-06-28.

Reviewer: xhigh `Poincare the 2nd`.

Verdict: PASS.  No required fixes.

## Checks

- The target-only `dEarly` call is in the positive-tail setup
  `M := M + 1`, while the recursive lower-left call itself uses `(M := M)` and
  index `0`.
- The rewrite orientation is sound: the comparison theorem states
  `targetOnly = sourceStaged`, so the new target-only bridge rewrites to the
  already-proved recursive source-staged bridge.
- The terminal `dLast#` expression is unchanged from the recursive predecessor.
- The noncommutative matrix order remains
  `- dEarly * coord.solvedA1 (Fin.last (M + 1))`.
- No theorem name, Lean statement, statement card, or prose claims a target-side
  linear equivalence, determinant-one normalizer, determinant equality,
  measure transport, normal crossings, pole order, RLCT, or analytic extraction.
- No `sorry`, `axiom`, `native_decide`, or `#exit` was introduced in the Lean
  diff or the two new notes.

The reviewer did not rerun Lean because the review assignment was read-only.
