# Statement card - A4 Case 2 free Cprime continuing branch

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Expected names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedFreeCprimeTop`
- `DLNFibre.DLN.Aoyagi.case2DisplayedFreeCprimeTail`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPostPivotFreeFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2DisplayedFreeCprime_eq_verticalBlock`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.postPivotFreeCprimeNextSameStageProduct`
- `DLNFibre.DLN.Aoyagi.sourceChartMap_postPivotFreeCprimeNextSameStageProduct_withCorrectedPostData`

## Statement

For the displayed Case 2 pivot chart, let `C'` be an arbitrary pivot-first
following matrix.  The lower rows of `D''' * C'`, reindexed to the next
same-stage residual row domain `(S,J+1)`, equal the post-pivot residual block
times the reindexed tail of `C'`.

The source-chart package combines this finite product identity with the
existing corrected post-data fields.

## Proved

- `C'` splits as a vertical block consisting of its pivot row and residual
  tail.
- Multiplication by `D''' = blockdiag(1,D-x*y)` sends the lower rows to
  `(D-x*y) * C'_tail`.
- The row and column complement equivalences reindex this product to the
  next same-stage domains.

## Assumed

- The displayed Case 2 pivot chart hypotheses.
- For the packaged theorem, the same supplied pre-state exponent, level,
  least-value-gap, and chart-family boundary hypotheses used by the existing
  source-chart continuing package.

## Cited

- None in Lean.  This is finite matrix algebra and finite reindexing.

## Deferred

- Source production of a free `C'` from a chart atlas.
- Arbitrary-pivot chart coverage.
- Chart regularity, Jacobian arithmetic, transition invariance, termination,
  normal crossings, pole order, and RLCT extraction.

## Review

- xhigh source checker `Erdos` confirmed the identity is source-faithful as a
  finite block-matrix adapter, with the arbitrary-`C'` scope restricted to a
  compatible displayed pivot-first chart-coordinate following factor.
- xhigh Lean API scout `Mill` confirmed the missing API is a free reindexed
  post-pivot following factor plus a free-`C'` lower-row theorem; the landed
  tail-split version is equivalent to the direct-submatrix API suggested in
  that scout.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
