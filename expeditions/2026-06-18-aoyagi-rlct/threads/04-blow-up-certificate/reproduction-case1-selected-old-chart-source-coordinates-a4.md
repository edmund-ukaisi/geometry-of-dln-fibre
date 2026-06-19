# A4 Case 1(1) Selected-Old Chart Source Coordinates

Status: pen-and-paper reproduced as a narrow row-wise source-coordinate
identity.

## Source Situation

Aoyagi's Case 1 chooses an old exceptional variable `u_(s,k)` with
`tilde_t_(s,k)=J+J1`, after a first gap

```text
b_(J+1) = ... = b_(J+J1).
```

The center printed on p. 16 consists of the row strip

```text
d_ij = 0,      J+1 <= i <= J+J1,    J+1 <= j <= M^(S+1),
```

together with the selected old generator `u_(s,k)=0`.

In Case 1(1), the selected chart denominator is the old variable itself.  The
source row-strip entries are divided by this old variable:

```text
d_ij = u_old * d'_ij        for J+1 <= i <= J+J1,
d_ij = d'_ij                below the strip.
```

This is distinct from Case 1(2), where the displayed pivot is the new variable
`u_(S,J+1)` and the old variable is factored as
`u_(s,k)=u_(S,J+1)u'_(s,k)`.  The `Q/P` calculation on pp. 17-18 belongs to
that displayed Case 1(2) branch, not to this Case 1(1) source-coordinate
identity.

## Calculation

Let `strip(i)` mean that the residual row level is at most `J+J1`.  Let
`u_old` be the selected old chart variable, `D'` the post-chart residual
matrix, and `b_pre(i)` the pre-chart row weight.

Define the source residual block by

```text
D_source(i,j) =
  u_old * D'(i,j),  if strip(i),
  D'(i,j),          otherwise.
```

Define the post row weights by

```text
b_post(i) =
  u_old * b_pre(i), if strip(i),
  b_pre(i),         otherwise.
```

Then the claimed matrix identity is

```text
diag(b_pre) * D_source = diag(b_post) * D'.
```

Entrywise, for any row `i` and column `j`,

```text
(diag(b_pre) * D_source)_(i,j) = b_pre(i) * D_source(i,j).
```

If `strip(i)`, this is

```text
b_pre(i) * (u_old * D'(i,j))
  = (u_old * b_pre(i)) * D'(i,j)
  = b_post(i) * D'(i,j).
```

If `not strip(i)`, this is

```text
b_pre(i) * D'(i,j) = b_post(i) * D'(i,j).
```

Thus the source-coordinate identity is purely elementary row-wise algebra.

## Lean Target

The Lean checkpoint should add:

```lean
case1SelectedOldPostWeight
case1SelectedOld_diagonal_mul_sourceMatrix
case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates
```

The source-coordinate specialization should use the existing residual-row
predicate `case1ResidualRowStrip n S J J1` and the source-coordinate residual
restriction `case2SourceResidualBlock residual`.

## Caveats

- No new label `(S,J+1)` is introduced in this Case 1(1) checkpoint.
- The chart denominator is the selected old variable `u_(s,k)`, not the
  displayed Case 1(2) pivot `u_(S,J+1)`.
- No `Q/P` source-order identity is asserted here.
- No chart coverage, regularity, Jacobian, transition invariant, normal
  crossings, or RLCT extraction is proved.
