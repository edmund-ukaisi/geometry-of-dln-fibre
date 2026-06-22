# Reproduction - Case 2 Source Current Row Reindex

Date: 2026-06-22.

Scope: finite row-index adapter for the continuing Case 2 source-following
matrix.  The adapter rewrites the pivot-first stack

```text
[ old top rows 1..J ; pivot row J+1 ; post-pivot rows J+2..n(S+1) ]
```

as the single source-ordered current row interval `1..n(S+1)`.

## Source-Order Index Split

The displayed continuation hypothesis gives

```text
J+1 <= prefixMinNat n (S+1) <= n(S+1).
```

Thus the current source row interval `1..n(S+1)` splits into three disjoint
pieces:

```text
1..J,
J+1,
J+2..n(S+1).
```

The first piece is `case2SourceOldTopRowIndex J`.  The second is `Unit`, the
displayed pivot row.  The third is the pivot complement of
`case2DisplayedPivotCol n hS hcont`, because that pivot column lives in the
old residual-column interval `J+1..n(S+1)` and deleting it leaves exactly the
post-pivot source rows.

This gives the finite equivalence

```text
case2SourceOldTopRowIndex J ⊕
  (Unit ⊕ pivotComplement (case2DisplayedPivotCol n hS hcont))
≃
case2SourceCurrentRowIndex n S.
```

## Old Following Block

Define the current source following block by restricting the source-coordinate
function `C` to rows `1..n(S+1)`.

Reindexing this block by the above equivalence gives:

```text
[ case2DisplayedSourceOldTopBlock C ;
  case2DisplayedSourceFollowingFactor n hS hcont C ].
```

The old top rows are tautological.  The pivot-first lower block is also
tautological: row `J+1` is `C(J+1)`, and every pivot-complement row `j` is
`C(j)`.

## Successor Following Block

Define the source successor following block by restricting
`case2DisplayedSourceSuccessorFollowingFactor` to the same current source row
interval.  This total source-coordinate function changes only row `J+1`,
replacing it by the top row of `Q^{-1}C`.

Reindexing the successor block gives:

```text
[ case2DisplayedSourceOldTopBlock C ;
  case2DisplayedPaperCprime n hS hcont residual C ].
```

Old top rows are unchanged because they are at most `J`.  The pivot row is the
top row of `case2DisplayedPaperCprime`, and each pivot-complement row is the
tail row of `case2DisplayedPaperCprime`.

## Lean Targets

```text
case2SourceCurrentRowIndex
case2SourceOldTopPaperCprimeRowEquiv
case2SourceCurrentFollowingBlock
case2SourceSuccessorFollowingBlock
case2SourceCurrentFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv
case2SourceSuccessorFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv
```

## Nonclaims

- No chart production of the successor following factor.
- No source production of `C'^(S+1)`.
- No source-suffix production.
- No recurrence or exponent post-data production.
- No transition invariant.
- No Jacobian arithmetic.
- No normal crossings, pole order, termination, or RLCT extraction.
