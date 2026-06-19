# A4 Case 1(2) Source-Weight Factored Boundary

Status: reproduced the elementary row-weight boundary between the original
source recurrence and the factored-base convention.

## Source Situation

In Case 1(2), Aoyagi factors the old selected variable

```text
old = u * old'
```

where `old` had source level `h = J + J1`. With the recurrence convention

```text
b_(r+1) = step_r * b_r,
```

the old source factor at level `h` first affects row `h+1`.

## Pen-And-Paper Calculation

Let `baseStep` be the recurrence after replacing `old` by `old'`. Let the
original source recurrence after substitution be

```text
sourceStep = mulStepAt baseStep u h.
```

For a residual row of source level `i`:

```text
i <= h:
  sourceWeight_i = baseWeight_i,

h + 1 <= i:
  sourceWeight_i = u * baseWeight_i.
```

This is exactly the row-weight convention already used in the displayed
row-strip source algebra:

```text
case1RowStripOldWeight strip u baseWeight
```

where `strip` is the predicate `i <= h`.

On residual-row indices, the canonical displayed Case 1 strip predicate is

```text
case2ResidualRowLevel i <= J + J1.
```

## Lean Boundary

Lean now defines

```text
case1ResidualRowStrip n S J J1
```

and proves that the row-strip old-weight convention is the same as the source
recurrence with the old selected factor still at level `J+J1`:

```text
case1ResidualRowStripOldWeight_eq_sourceMulStepAt
```

It also combines this identification with the existing row-strip source-matrix
identity:

```text
case1ResidualRowStrip_diagonal_mul_sourceMatrix_sourceWeights
```

The resulting identity says that weighting the row-strip source matrix by the
original source recurrence is equal to weighting the normalised matrix by
`u * baseWeight` on every residual row.

## Caveats

- This does not construct `baseStep` from source coordinates.
- This does not prove hidden old-label source validity.
- This does not prove chart production or post-data production.
- This does not prove chart coverage, regularity, Jacobian accounting, normal
  crossings, or RLCT extraction.
