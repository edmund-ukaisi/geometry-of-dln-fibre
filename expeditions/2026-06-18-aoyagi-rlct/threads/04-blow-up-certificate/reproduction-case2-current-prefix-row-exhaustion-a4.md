# A4 Case 2 Current-Prefix Row Exhaustion

Status: reproduced the finite-domain fact that current-prefix exhaustion
empties the displayed pivot's row complement.  This is not actual-width
exhaustion and not construction of the terminal following matrix.

## Source Anchor

Aoyagi's displayed Case 2 residual block has active rows

```text
J+1 <= i <= M(S).
```

In the repo notation this current prefix width is `prefixMinNat n S`.  The
displayed pivot is the first residual row, `i = J+1`.

## Pen-And-Paper Reproduction

After the displayed pivot, the post-pivot residual rows are

```text
J+2 <= i <= prefixMinNat n S.
```

If current-prefix row exhaustion holds,

```text
prefixMinNat n S = J+1,
```

then there is no `i` satisfying

```text
J+2 <= i <= prefixMinNat n S.
```

Therefore the finite post-pivot row set is empty.

The displayed pivot row complement is equivalent to this post-pivot row set.
Hence the displayed pivot's row complement is empty.

## Lean Shape

Lean already had:

```text
case2PostPivotRows_eq_empty_of_prefixMin_current_eq
case2DisplayedPivotRowComplement_isEmpty_of_postPivotRows_eq_empty
```

The new theorem composes them:

```text
case2DisplayedPivotRowComplement_isEmpty_of_prefixMin_current_eq
```

## Boundaries

- This identifies the row-exhausted side under current-prefix exhaustion.
- It does not assert actual-width exhaustion.
- It does not assert that the column complement is empty.
- It does not construct `C'^(S+1)` or choose the complete terminal row/column
  presentation in source order.
- It does not prove chart production, chart coverage or regularity, Jacobian
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariance, automatic Case 2 gap/tail transport, or printed-vector repair.

## Kill Conditions

- Do not use actual-width exhaustion `n(S+1)=J+1` in place of
  `prefixMinNat n S=J+1`.
- Do not attach this row-side fact as a projection of the actual-width terminal
  source model without an independent row-exhaustion hypothesis.
