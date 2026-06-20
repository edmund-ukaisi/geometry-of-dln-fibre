# Review - A4 Case 2 Terminal Frontier Bridges

Status: passed xhigh source/math and Lean/API review.

## Source/Math Review

No blocking source/math fidelity issues were found.

- Aoyagi's stopped branch uses terminal prefix rows `1..M(S+1)`, and under
  `J+1<=M(S+1)` plus not `J+2<=M(S+1)` this is exactly `1..J+1`.
- The current source terminal candidate does not miss terminal prefix rows.
  It can miss actual next-layer rows in the row-exhausted wide-next case, but
  those are not part of the advanced terminal prefix object.
- The top row of `Q^-1 C` is the original pivot-column row plus the
  displayed pivot-row weighted sum over the post-pivot actual columns. This
  is exactly the first-row multiplication by `[1 y]`.
- The supplied terminal matrix bridge is the correct handoff shape: it records
  old-row and pivot-row equations as assumptions rather than claiming chart
  production.
- The named `SuppliedTerminalCprimeBridge` structure is appropriate boundary
  data for a future chart-production theorem.

## Lean/API Review

No blocking Lean/API issues were found.

- The prefix-row layer uses equivalence reindexing and entry-ideal invariance,
  reusing `case2_next_frontier_eq_of_cont_of_not_next`,
  `Matrix.submatrix_mul_equiv`, and `matrixEntryIdeal_submatrix_equiv`.
- The supplied terminal matrix bridge is extensional on terminal rows and then
  reuses the already proved product-form theorem.
- The bridge structure projections are thin wrappers around the row-equation
  equality and product rewrite.
- The bridge-consuming prefix and source-suffix wrappers only rewrite through
  `SuppliedTerminalCprimeBridge`; they do not construct a bridge or add hidden
  source-production assumptions.
- The new prefix-row source-suffix wrapper is a direct composition of the
  existing terminal-prefix product theorem with
  `SuppliedTerminalCprimeBridge.terminalPrefixProduct_eq_weight_mul_CtermPrefix_mul`.

## Residual Risk

The bridges move the formal frontier but do not produce Aoyagi's chart
coordinates.  A future theorem must construct the supplied terminal matrix
and prove the old-row and pivot-row equations from the displayed source chart.

## 2026-06-20 Actual-Width Original-Row Addendum

No blocking source/math or Lean/API issues were found in the actual-width
original-row specialization.

- The specialization is scoped to `n(S+1)=J+1`.
- It uses only the empty displayed pivot-column complement to kill the
  correction sum in the top row of `Q^-1 C`.
- It correctly identifies that top row with the original source row
  `C(J+1,-)`.
- The downstream original-row terminal theorem remains a bridge consumer and
  does not claim chart production, suffix construction, Jacobian arithmetic,
  normal crossings, or RLCT extraction.

Residual caveat: this addendum reviews the local actual-width exhausted Case 2
bridge and its immediate consumer.  It does not certify the broader chart
coverage or RLCT pipeline.
