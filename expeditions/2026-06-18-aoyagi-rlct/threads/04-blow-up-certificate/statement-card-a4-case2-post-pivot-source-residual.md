# Statement card - A4 Case 2 post-pivot source residual

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedPostPivotSourceResidual`
- `DLNFibre.DLN.Aoyagi.case2SourceResidualBlock_postPivotSourceResidual`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_sourceFollowingFactor`

## Statement

Lean now names a source-coordinate representative for the displayed Case 2
post-pivot lower-right block.  The representative agrees with
`case2DisplayedPostPivotResidualBlock` on the next same-stage residual domain
`(S,J+1)` and is zero outside that finite row/column rectangle.

Restricting the representative with `case2SourceResidualBlock` at `(S,J+1)`
recovers the displayed post-pivot residual block.  The existing lower-row
identity for `D''' * C'` can therefore be rewritten using both
`case2SourceResidualBlock` and the next same-stage
`case2SourceFollowingFactor`.

## Proved

- A total source-coordinate function `case2DisplayedPostPivotSourceResidual`
  represents the post-pivot lower-right block by zero extension.
- Restricting this function to the next same-stage residual row and column
  domains recovers `case2DisplayedPostPivotResidualBlock`.
- The paper `C' = Q^-1 C` lower-row product has a source-residual/source-
  following notation form.

## Assumed

- Displayed Case 2 pivot validity: `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.
- Source residual coordinates and following factor are supplied as functions.

## Cited

- None in Lean.  This is finite reindexing and matrix algebra.

## Deferred

- Chart production of the source representative.
- Source-produced successor recurrence or exponent post-data.
- Successor chart-family construction and transition invariance.
- Atlas coverage, arbitrary pivot coverage, coordinate regularity, Jacobian
  arithmetic, normal crossings, pole order, RLCT extraction, terminal
  relabeling, and printed-vector repair.

## Review

- Landed-patch review passed by xhigh `Bacon`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
