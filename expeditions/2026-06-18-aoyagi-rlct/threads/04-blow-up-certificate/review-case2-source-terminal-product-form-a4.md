# Review - A4 Case 2 Source Terminal Product Form

Status: passed xhigh source/math and Lean/API review.

## Source/Math Review

No blocking source/math fidelity issues were found.

- The statement is the right next narrow target after the source terminal
  product candidate: it is pure reindexing algebra.
- Product orientation matches the Aoyagi terminal display:
  `diag(...) * C'^(S+1) * prod_{s=S+2}^L C^(s)`.
- The row equivalence direction is correct: source-row pullback uses
  `(case2SourceTerminalRowEquiv J).symm`.
- The theorem needs no failed-next-continuation hypothesis; it only needs the
  continuation parameters used by the candidate definitions.

## Lean/API Review

No blocking Lean/API issues were found.

The proof uses `Matrix.submatrix_mul_equiv` twice.  The only Lean hazard was
identity-map normalization: the outer final-column map normalizes as `id`,
while the intermediate `τ` identity is matched through `Equiv.refl τ`.

## Residual Risk

This theorem closes the product-form packaging gap for the existing reindexed
candidate.  It still does not prove that the source terminal `C'` candidate is
chart-produced or that Aoyagi's full `C'^(S+1)` has been constructed.
