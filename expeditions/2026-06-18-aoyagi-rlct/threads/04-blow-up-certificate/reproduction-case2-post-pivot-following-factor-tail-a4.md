# Pen-and-paper reproduction - Case 2 post-pivot following-factor tail

Status: checked finite following-factor tail identity for Aoyagi's displayed
Case 2 pivot.

This note isolates a narrow consequence of Aoyagi's column operation
`C' = Q^-1 C`: the lower rows of `C'` are unchanged.  After deleting the
displayed pivot column, the post-pivot following-factor candidate is therefore
the original source following factor restricted to the next same-stage
residual columns `(S,J+1)`.

It does not prove chart-produced recurrence data, exponent data, a successor
chart-family boundary, transition invariance, Jacobian arithmetic, normal
crossings, RLCT extraction, terminal relabeling, arbitrary pivot coverage, or
repair of the printed Case 2 vector.

## Source

Aoyagi PDF pp. 19-22, displayed Case 2:

- the pivot-first normalised residual block has top row `[1 y]`;
- the column operation uses

```text
Q^-1 = [1  y]
       [0  I],
```

- the following factor is replaced by `C' = Q^-1 C`;
- the continuing branch deletes the displayed pivot column and advances from
  `J` to `J+1` at the same stage.

## Reproduction

Write the pivot-first following factor as

```text
C = [C_0]
    [C_tail].
```

Then

```text
C' = Q^-1 C
   = [1  y] [C_0]
     [0  I] [C_tail]
   = [C_0 + y C_tail]
     [C_tail].
```

Thus the lower tail of `C'` is exactly `C_tail`; only the pivot row is changed.

The displayed pivot column complement is the old residual-column domain with
`J+1` deleted.  The post-pivot domain handoff identifies that complement with
the next same-stage residual-column domain

```text
Case2ResidualColIndex(n,S,J+1),
```

whose raw source columns are `J+2..M^(S+1)`.  Therefore the reindexed
post-pivot following-factor candidate is entrywise

```text
C_next(j,a) = C(j,a)
```

for `j` in the next same-stage residual-column domain.

## Lean target

Add:

```text
pivotQinv_mul_tail_apply
case2DisplayedPaperCprimeTail_apply
case2DisplayedPostPivotFollowingFactor_eq_sourceFollowingFactor_succ
```

The last theorem should state:

```text
case2DisplayedPostPivotFollowingFactor n hS hcont residual C =
  case2SourceFollowingFactor (n := n) (S := S) (J := J+1) C.
```

## Kill conditions

- Do not call this Aoyagi's full next `C'^(S+1)`.
- Do not claim chart production of recurrence or exponent post-data.
- Do not claim transition invariance or chart coverage.
- Keep the next columns as actual source-width columns `J+2..M^(S+1)`, not a
  prefix-width substitute.
- Do not attach normal crossings, RLCT extraction, Jacobian arithmetic,
  terminal relabeling, arbitrary pivot coverage, or printed-vector repair.
