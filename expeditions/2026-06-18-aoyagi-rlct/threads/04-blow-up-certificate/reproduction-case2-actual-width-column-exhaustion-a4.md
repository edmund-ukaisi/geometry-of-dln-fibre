# A4 Case 2 Actual-Width Column Exhaustion

Status: reproduced the finite-domain fact that actual next-width exhaustion
empties the displayed pivot's column complement.  This is not a construction of
the terminal following matrix.

## Source Anchor

Aoyagi's displayed Case 2 residual block has active columns

```text
J+1 <= j <= M^(S+1).
```

In the repo notation this actual next width is `n(S+1)`.  The displayed pivot
is the first residual column, `j = J+1`.

## Pen-And-Paper Reproduction

After the displayed pivot, the post-pivot residual columns are

```text
J+2 <= j <= n(S+1).
```

If actual next-width exhaustion holds,

```text
n(S+1) = J+1,
```

then there is no `j` satisfying `J+2 <= j <= n(S+1)`.  Therefore the finite
post-pivot column set is empty.

The displayed pivot column complement is equivalent to this post-pivot column
set.  Hence the displayed pivot's column complement is empty.

## Lean Shape

Lean already had:

```text
case2PostPivotCols_eq_empty_of_width_next_eq
case2DisplayedPivotColComplement_isEmpty_of_postPivotCols_eq_empty
```

The new theorem composes them:

```text
case2DisplayedPivotColComplement_isEmpty_of_width_next_eq
```

The source-model projection is:

```text
Case2DisplayedSuppliedActualWidthTerminalSourceModel.displayedPivotColComplement_isEmpty
```

## Boundaries

- This identifies the exhausted side under actual-width exhaustion.
- It does not assert that the row complement is empty.
- It does not construct `C'^(S+1)` or choose the complete terminal
  row/column presentation in source order.
- It does not prove chart production, chart coverage or regularity, Jacobian
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, automatic Case 2 gap/tail transport, or printed-vector repair.

## Kill Conditions

- Do not use prefix exhaustion in place of `n(S+1)=J+1`.
- Do not infer that all following-factor data are source-produced from column
  complement emptiness alone.
