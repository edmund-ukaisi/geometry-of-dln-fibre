# Review - A2 fixed-base adapted endpoint Frobenius comparison

Date: 2026-06-25.

Reviewer: xhigh independent reviewer Sagan the 5th; focused Lean build.

## Verdict

No blocking issues found.

## Checks

- The Lean claim is the fixed-coordinate identity
  `trace((T - T0)^T (T - T0)) = finite entry square-sum`; it does not identify
  this with the original `lossDLN`.
- The endpoint orientation is consistent: the total matrix has rows at target
  endpoint `Fin.last N` and columns at source endpoint `0` for the reversed
  chain.  At `E = reverseEdge W B`, `chainMap_reverse_eq_paper` identifies the
  product with `paperTotalMap`, and the existing adapted endpoint theorem gives
  `[[I,0],[0,0]]`.
- The Frobenius product-reduction theorems are rewrite wrappers over the
  existing adapted square-sum bounds.  No original-loss, statistical-loss, or
  basis-change comparability claim is introduced.
- The reproduction and statement card accurately record the boundary.  The
  reviewer requested only wording precision around the endpoint zero blocks and
  an explicit row/column orientation note; both were incorporated.
- `lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates` passed
  after the Lean implementation.

## Boundary

This slice proves only the fixed adapted endpoint Frobenius identity and its
direct use in already-landed finite p. 13 bounds.  It does not compare with
`lossDLN`, does not prove original-coordinate norm equivalence, does not
construct an analytic product chart, does not transport density or Jacobian
factors, and does not prove normal crossings, pole order, or RLCT extraction.
