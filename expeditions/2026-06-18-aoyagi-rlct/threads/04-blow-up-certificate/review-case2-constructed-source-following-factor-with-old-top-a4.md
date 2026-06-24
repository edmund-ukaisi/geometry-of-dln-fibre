# Review - Case 2 constructed source following factor with old top rows

Date: 2026-06-24.

Reviewer: xhigh subagent Ampere the 2nd.

## Verdict

Accept with small weakenings.  No blocking mathematical issue.

The old-top/residual construction is sound finite bookkeeping.  The source rows
`1,...,J` and the residual following-factor rows `J+1,...,n(S+1)` are
disjoint, and Aoyagi's displayed Case 2 operation `Q^-1` acts only on the
residual block `C_J^(S+1)`.  The old rows are carried separately into the
stacked source-row presentation, matching the Lean split between
`case2DisplayedSourceOldTopBlock`, `case2DisplayedSourceFollowingFactor`, and
`case2DisplayedPaperCprime`.

## Required Boundary Corrections

- The current block is stacked over the old residual block, not over the
  transported `C'` in general.
- For arbitrary residual data `Csrc`, the successor block has lower part
  `Q^-1*Csrc`; the lower part is `Cprime` only in the specialized construction
  `Csrc = Q*Cprime`.
- The source-current row interval is the actual-width interval
  `1,...,n(S+1)`, not the prefix-minimum interval.
- The tail calculation should be packaged through the whole recovery theorem
  `paperCprime = Cprime`.

These corrections have been incorporated into the reproduction and Lean target
shape.

## Nonclaims

The reviewed target remains finite source-coordinate bookkeeping.  It does not
claim chart coverage, source production, transition regularity, normal
crossings, pole order, or RLCT extraction.
