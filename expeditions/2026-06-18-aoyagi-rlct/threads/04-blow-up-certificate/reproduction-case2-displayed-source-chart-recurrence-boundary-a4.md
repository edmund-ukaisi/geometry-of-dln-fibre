# A4 Case 2 Displayed Source-Chart Recurrence Boundary

Status: reproduced the recurrence-only boundary connecting Aoyagi's displayed
top-left Case 2 source chart variable to the concrete successor recurrence
state.  This is not a chart-production theorem.

## Source Anchor

On PDF pp. 19-21 Aoyagi's Case 2 center is the residual block

```text
d_ij = 0,    i = J+1,...,M(S),    j = J+1,...,M^(S+1).
```

The displayed top-left chart writes the block as

```text
d_(J+1,J+1) = u_(S,J+1),
d_ij = u_(S,J+1) d'_ij    off the selected entry,
```

and then records the recurrence update

```text
b'_(J+1) = u_(S,J+1) b_(J+1),
...
b'_(M(S)) = u_(S,J+1) b_(M(S)).
```

## Pen-And-Paper Reproduction

Let `pre` be the recurrence state at `(S,J)`.  Define the concrete successor
state

```text
post = pre.case2Succ u.
```

By definition of `case2Succ`,

```text
post.level(S,J+1) = J,
post.var(S,J+1) = u,
```

and every old introduced label has the same level and variable as in `pre`.
Thus `post` satisfies the recurrence post-data package for the variable `u`.

The displayed source chart map has pivot value

```text
case2DisplayedSourceChartMap(..., u, residual)(J+1,J+1) = u.
```

Therefore the same concrete post-data package can be read as using the
displayed source chart's pivot coordinate as the new recurrence variable.

The recurrence weight attached to row `i` is the monomial recurrence product
up to `i`.  Adding a new label at level `J` with variable `u` multiplies exactly
the step at level `J`.  Hence for every `i >= J+1`,

```text
post.weight(i) = u * pre.weight(i).
```

Replacing `u` by the displayed pivot value gives

```text
post.weight(i)
  = case2DisplayedSourceChartMap(...)(J+1,J+1) * pre.weight(i).
```

For a residual-row subtype index `r`, Lean's row level satisfies
`J+1 <= case2ResidualRowLevel n S J r`, so the same identity specializes to
all rows in the Case 2 residual block.

## Boundaries

- The source chart map is used only through its displayed pivot value.
- This does not construct the affine blow-up chart.
- This does not prove chart-produced exponent post-data or Jacobian/volume
  arithmetic.
- This does not prove chart coverage, coordinate regularity, normal crossings,
  RLCT extraction, termination, transition invariance, or repair of the printed
  Case 2 vector mismatch.
