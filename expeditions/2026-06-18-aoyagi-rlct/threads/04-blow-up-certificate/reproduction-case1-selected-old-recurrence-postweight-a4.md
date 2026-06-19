# A4 Case 1(1) Selected-Old Recurrence Post Weights

Status: pen-and-paper reproduced as a pure recurrence calculation with a
supplied base recurrence.

## Source Situation

In Aoyagi Case 1(1), the selected denominator is the old exceptional variable
`u_(s,k)` itself.  The source lowers the selected old label from level
`J+J1` to level `J`.  On PDF p. 16 this is reflected in the row weights on
the selected strip:

```text
b'_(J+1) = u_(s,k) b_(J+1), ..., b'_(J+J1) = u_(s,k) b_(J+J1).
```

Rows below the strip are not printed in the same display, but they follow from
the recurrence interpretation: after the selected factor has moved from level
`J+J1` down to level `J`, rows strictly below `J+J1` already contained that
factor in the old recurrence and still contain it in the lowered recurrence.

## Calculation

Let `baseStep` be a supplied recurrence with the selected old factor removed
as a separate factor.  Do not try to cancel this factor out of arbitrary
source recurrence data.

Set

```text
h = J + J1,
b_i       = monomialRec(mulStepAt(baseStep,u,h), i),
b'_i      = monomialRec(mulStepAt(baseStep,u,J), i).
```

For an active residual row, `i >= J+1`.

If `i <= h`, then the old factor at level `h` has not appeared in `b_i`, while
the lowered factor at level `J` has appeared in `b'_i`:

```text
b_i  = monomialRec(baseStep,i),
b'_i = u * monomialRec(baseStep,i) = u * b_i.
```

If `i > h`, then both recurrences contain exactly one copy of `u`:

```text
b_i  = u * monomialRec(baseStep,i),
b'_i = u * monomialRec(baseStep,i),
```

so `b'_i = b_i`.

Therefore on residual rows

```text
b'_i =
  u * b_i, if i <= J+J1,
  b_i,     otherwise.
```

This is exactly the piecewise post-weight convention
`case1SelectedOldPostWeight (case1ResidualRowStrip n S J J1) u b`.

## Lean Target

Add the pure recurrence and residual-row forms:

```lean
monomialRec_mulStepAt_case1_selectedOld_postWeight
case1SelectedOldPostWeight_eq_monomialRec_loweredLevel
case1SelectedOld_diagonal_mul_sourceMatrix_loweredLevel
case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates_loweredLevel
```

The matrix identities should combine the already proved Case 1(1) row-strip
source identity with the recurrence post-weight equality.  They should use
only a supplied base recurrence `step`.

## Caveats

- This does not construct the selected-old chart.
- This does not prove that a recurrence state actually has `baseStep` as its
  selected-factor-removed recurrence.
- This does not introduce `(S,J+1)` and does not use the displayed Case 1(2)
  pivot `u_(S,J+1)`.
- This does not assert `Q/P`, chart coverage, regularity, Jacobian, normal
  crossings, RLCT extraction, or a transition invariant.
