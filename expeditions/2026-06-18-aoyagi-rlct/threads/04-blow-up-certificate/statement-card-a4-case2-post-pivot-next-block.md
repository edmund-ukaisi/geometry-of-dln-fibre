# Statement card - A4 Case 2 post-pivot next block

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.weightedPivotClearedBlock_mul_verticalBlock`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPostPivotResidualBlock`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPostPivotFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPostPivotResidualBlock_nonempty_of_next`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct`

## Statement

Lean now packages the continuing displayed Case 2 lower-right block after the
pivot as supplied same-stage `(S,J+1)` data.

The cleared lower-right block `D - x*y` is reindexed to
`Case2ResidualRowIndex n S (J+1)` by
`Case2ResidualColIndex n S (J+1)`, and the tail of the transported following
factor `C' = Q^-1 C` is reindexed to the next same-stage column domain.  The
lower rows of `D''' * C'`, after the same row reindexing, equal the product of
these two supplied next-block objects.

## Proved

- General block multiplication:
  `weightedPivotClearedBlock D * verticalBlock Ctop Ctail =
  verticalBlock Ctop (D * Ctail)`.
- The displayed Case 2 post-pivot residual block and following-factor tail can
  be named over the next same-stage residual row/column types.
- Under `J+2 <= prefixMinNat n (S+1)`, the next same-stage residual center is
  nonempty.
- The lower part of the paper expression `D''' * C'` reindexes to
  `case2DisplayedPostPivotResidualBlock *
  case2DisplayedPostPivotFollowingFactor`.

## Assumed

- Current displayed pivot validity: `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.
- The continuing-branch nonemptiness theorem additionally assumes
  `J+2 <= prefixMinNat n (S+1)`.
- The residual source coordinates and following factor are supplied as
  functions/matrices.

## Cited

- None in Lean.  This is finite matrix algebra and reindexing.

## Deferred

- Chart production of the residual/following-product data.
- Recurrence/exponent post-data from coordinates.
- Chart coverage, coordinate regularity, transition invariance, Jacobian
  arithmetic, normal crossings, RLCT extraction, arbitrary pivot coverage, and
  the terminal `(S+1,0)` relabel branch.
- Repair of Aoyagi's printed Case 2 vector mismatch.

## Review

- Source/target shape checked by xhigh `Ptolemy the 5th` and Lean API checked
  by xhigh `Noether the 5th`.
- Landed-patch review passed by xhigh `Plato`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
