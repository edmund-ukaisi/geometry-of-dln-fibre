# Review - A4 Case 2 source-chart arbitrary-suffix actual-width boundary

Reviewed objects:

- `exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
- `sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary`
- `reproduction-case2-source-chart-arbitrary-suffix-actual-width-a4.md`
- `statement-card-a4-case2-source-chart-arbitrary-suffix-actual-width.md`

Verdict: no blocking source/math or Lean API issue found.

The slice keeps `F` supplied, uses actual-width exhaustion `n(S+1)=J+1` for
the original-row bridge, and keeps the row-exhausted transported-row branch
separate.  The concrete source-chart wrapper fixes the successor recurrence
state and corrected selected-label exponent data by using the displayed
source-chart constructor, but it does not produce the following matrix.

## Nonblocking Suggestions Applied

- The reproduction now writes the left factor as a block-diagonal matrix rather
  than pseudo-addition.
- The recovery of the source-suffix theorem now mentions both
  `hSuffix : S+1 <= L` and the specialization of `τ` to the source-layer type.
- The statement card now lists the continuing stage/continuation, exponent,
  level, gap, and `chartFamily` hypotheses.

## Caveats

- `F` is supplied.
- Actual-width original rows do not follow from row exhaustion.
- No chart coverage, normal-crossing/RLCT, transition invariant, or
  source-produced `C'^(S+1)` theorem is proved.
