# Pen-and-paper reproduction - Case 2 post-pivot domain handoff

This note isolates finite domain bookkeeping in Aoyagi's displayed Case 2
blow-up step.  It does not prove chart coverage, source production of the next
matrix `C'^(S+1)`, transition invariance, Jacobian arithmetic, normal
crossings, or RLCT extraction.

## Source

Aoyagi PDF pp. 19-22, Case 2:

- the displayed pivot is the upper-left residual entry at source row and
  column `J+1`;
- after the `Q/P` operations, the lower-right residual block has rows and
  columns strictly after this pivot;
- the continuation condition for another `J`-advance is that the next pivot
  `J+2` is still within the prefix-minimum range.

This note records only the finite row/column domains that result from deleting
the displayed pivot row and column.

## Existing Lean domains

The current residual center at state `(S,J)` is

```text
Rows(S,J) = { i : J+1 <= i <= M(S) },
Cols(S,J) = { k : J+1 <= k <= M^(S+1) },
Entries(S,J) = Rows(S,J) x Cols(S,J).
```

Lean names these:

```text
case2ResidualBlockRows n S J
case2ResidualBlockCols n S J
case2ResidualBlockPivotEntries n S J
```

The lower-right block after selecting the displayed pivot `(J+1,J+1)` removes
that first row and column:

```text
PostRows(S,J) = { i : J+2 <= i <= M(S) },
PostCols(S,J) = { k : J+2 <= k <= M^(S+1) },
PostEntries(S,J) = PostRows(S,J) x PostCols(S,J).
```

Lean already names these:

```text
case2PostPivotRows n S J
case2PostPivotCols n S J
case2PostPivotEntries n S J
```

## Domain handoff

The residual center at the next same-stage state `(S,J+1)` is

```text
Rows(S,J+1) = { i : (J+1)+1 <= i <= M(S) },
Cols(S,J+1) = { k : (J+1)+1 <= k <= M^(S+1) },
Entries(S,J+1) = Rows(S,J+1) x Cols(S,J+1).
```

Since `(J+1)+1 = J+2`, these are exactly

```text
PostRows(S,J) = Rows(S,J+1),
PostCols(S,J) = Cols(S,J+1),
PostEntries(S,J) = Entries(S,J+1).
```

This is a definitional finite-domain handoff, not a statement that the source
chart has produced the next residual matrix.

## Nonemptiness / next continuation

The post-pivot entry set is nonempty iff both the row and column post-pivot
ranges are nonempty:

```text
J+2 <= M(S)       and       J+2 <= M^(S+1).
```

Because

```text
M(S+1) = min(M(S), M^(S+1)),
```

this is equivalent to

```text
J+2 <= M(S+1).
```

Lean already proves this as

```text
case2PostPivotEntries_nonempty_iff_next_cont
```

The next handoff wrapper should restate the same fact for
`case2ResidualBlockPivotEntries n S (J+1)`.

## Lean target

Add near the existing `case2PostPivotRows` definitions:

```text
case2PostPivotRows_eq_case2ResidualBlockRows_succ
case2PostPivotCols_eq_case2ResidualBlockCols_succ
case2PostPivotEntries_eq_case2ResidualBlockPivotEntries_succ
case2ResidualBlockPivotEntries_succ_nonempty_iff_next_cont
```

Add near the existing pivot-complement equivalences:

```text
case2DisplayedPivotRowComplementEquivResidualRowSucc
case2DisplayedPivotColComplementEquivResidualColSucc
```

These equivalences should be definitional or transported through the finite-set
equalities.  They say only that deleting the displayed pivot row/column gives
the next same-stage residual row/column index types.

## Kill conditions

- Do not identify this with a full Case 2 transition theorem.
- Do not claim source production of `C'^(S+1)` or the following product.
- Do not use the terminal `(S+1,0)` relabel here.
- Keep row-prefix exhaustion `M(S)=J+1` separate from actual-width exhaustion
  `M^(S+1)=J+1`.
- Do not attach chart coverage, transition regularity, Jacobian, normal
  crossings, or RLCT consequences.
