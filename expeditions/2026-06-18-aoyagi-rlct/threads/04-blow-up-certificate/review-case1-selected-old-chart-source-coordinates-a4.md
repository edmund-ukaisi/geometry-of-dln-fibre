# Review - A4 Case 1(1) Selected-Old Chart Source Coordinates

Reviewer: xhigh subagent `Anscombe the 3rd`.

Status: passed after a low-severity docstring fix.

## Findings

The reviewer found no medium or high severity issues.

One low-severity reader-facing hazard was identified: the shared helpers
`case1RowStripSourceMatrix` and `case1ResidualRowStrip` had docstrings that
still sounded Case 1(2)-specific.  Since the new Case 1(1) theorem reuses
these helpers with the selected old chart denominator, this could confuse
`u_(s,k)` with the displayed Case 1(2) pivot `u_(S,J+1)`.

The controller fixed this by broadening those docstrings:

- `case1RowStripSourceMatrix` now says the scalar `u` is the selected old
  chart denominator in Case 1(1) and the displayed row-strip pivot in Case
  1(2).
- `case1ResidualRowStrip` now says the same finite predicate marks the divided
  rows in both Case 1 branches, with the chart denominator supplied
  separately.

## Source-Fidelity Verdict

The new Lean theorem is source-faithful for its narrow target:

```text
diag(pre weights) * source row-strip matrix
  = diag(post weights absorbing u_old on the strip) * post residual matrix.
```

It does not use or mention the displayed Case 1(2) pivot row/column.  It does
not assert a `Q/P` source-order transition, chart construction, atlas
coverage, regularity, Jacobian, normal crossings, or RLCT extraction.

Residual rows and residual columns remain separated by the existing
`Case2ResidualRowIndex` and `Case2ResidualColIndex` domains: rows use the
prefix-minimum residual range, while columns use the actual active width.

## Residual Risk

This is only the elementary row-wise algebra for Case 1(1).  A full selected
old chart theorem still needs supplied Case 1 first-jump hypotheses, selected
old label semantics, exponent-update production, and chart/transition data.
