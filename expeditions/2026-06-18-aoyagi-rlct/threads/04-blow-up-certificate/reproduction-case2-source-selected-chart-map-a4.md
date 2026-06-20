# A4 Case 2 Source-Selected Chart-Map Adapter

Status: reproduced the finite source-coordinate adapter for a supplied Case 2
residual-block pivot.  This is not a chart-coverage theorem and not a claim
that Aoyagi displays non-top-left source charts.

## Source Anchor

Aoyagi's Case 2 center is the residual block

```text
d_ij = 0,    i = J+1,...,M(S),    j = J+1,...,M^(S+1).
```

In the displayed top-left chart the source writes the block as

```text
D_J = u_(S,J+1) * D'_J,
```

with the selected entry normalized to `1`, then introduces the new recurrence
factor and performs the `Q/P` operations.  See the PDF pp. 19-21.

The Lean checkpoint abstracts only the selected-entry finite algebra: if a
pivot `p` is already supplied as an element of the finite residual-block
center, define the same selected-entry chart map at that supplied pivot.

## Pen-And-Paper Reproduction

Let

```text
E = { (i,j) | J+1 <= i <= M(S), J+1 <= j <= M^(S+1) }.
```

Fix a supplied pivot `p = (i0,j0) in E`.  The selected-entry chart map is

```text
Phi_p(u, r)_p = u,
Phi_p(u, r)_q = u * r_q          for q != p.
```

The normalized map is

```text
N_p(r)_p = 1,
N_p(r)_q = r_q                  for q != p,
```

so pointwise

```text
Phi_p(u,r)_q = u * N_p(r)_q.
```

Lean's residual block uses subtype indices:

```text
i : Case2ResidualRowIndex n S J,
j : Case2ResidualColIndex n S J.
```

The supplied membership proof `hp : p in E` gives subtype pivots

```text
row = case2ResidualBlockPivotRowOfMem hp,
col = case2ResidualBlockPivotColOfMem hp.
```

The bookkeeping identity is

```text
(i.val, j.val) = p    iff    (i,j) = (row,col).
```

Therefore the source-coordinate restricted block

```text
(i,j) |-> Phi_p(u,r)_(i.val,j.val)
```

is exactly the existing selected-entry substitution matrix

```text
case2SourceSelectedSubstitutionMatrixOfMem hp u r.
```

Similarly, the restricted normalized block is exactly

```text
case2SourceSelectedNormalizedMatrixOfMem hp r.
```

Finally, the existing source-selected supplied-boundary theorem
`sourceSelectedQP` is transported across these two equalities.  The pivot row
weight remains

```text
post.weight (case2ResidualRowLevel n S J row),
```

not the displayed top-left specialization `post.weight (J+1)`.

## Boundaries

- The pivot `p` is supplied.
- This does not prove atlas coverage.
- This does not assert that Aoyagi displays arbitrary non-top-left charts.
- This does not prove chart-produced recurrence or exponent post-data.
- This does not compute Jacobians, prove normal crossings, extract RLCT, prove
  termination, prove transition invariance, or repair the printed Case 2
  vector mismatch.
