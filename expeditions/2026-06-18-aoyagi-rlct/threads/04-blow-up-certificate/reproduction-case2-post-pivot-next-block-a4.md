# Pen-and-paper reproduction - Case 2 post-pivot next block

This note isolates the continuing-branch algebra after Aoyagi's displayed
Case 2 pivot.  It is a reindexing and product-shape checkpoint only.  It does
not prove chart coverage, coordinate regularity, recurrence/exponent
post-data from coordinates, Jacobian arithmetic, normal crossings, RLCT
extraction, termination, transition invariance, arbitrary pivot coverage, or
the terminal `(S+1,0)` relabel branch.

## Source

Aoyagi PDF pp. 19-22, Case 2:

- the displayed residual block before pivoting has rows `J+1..M(S)` and
  columns `J+1..M^(S+1)`;
- after selecting the displayed pivot `(J+1,J+1)`, the `Q` column operation
  replaces the following factor by `C' = Q^-1 C`;
- the `P` row operation clears the first column below the pivot and leaves a
  lower-right block;
- in the continuing branch, that lower-right block has rows and columns
  strictly after the pivot and is the residual block for the next same-stage
  state `(S,J+1)`.

The previous checkpoint proved the finite domain equality.  This note adds the
matrix product shape over those domains.

## Pen-and-paper derivation

Write the pivot-first normalised block as

```text
D_chart = [1  y]
          [x  D].
```

The paper's column operation is

```text
Q = [1 -y]
    [0  I ],
```

so

```text
D'' = D_chart Q = [1 0]
                      [x E],
where E = D - x y.
```

The transported following factor is

```text
C' = Q^-1 C = [C'_0]
              [C'_tail].
```

After the row operation `P`, the cleared block is

```text
D''' = [1 0]
       [0 E].
```

Hence, purely by block multiplication,

```text
D''' C' = [C'_0]
          [E C'_tail].
```

The previous post-pivot domain handoff identifies the lower-row index type
with rows `J+2..M(S)` and the lower-column index type with columns
`J+2..M^(S+1)`, equivalently the next same-stage residual row/column domains
at `(S,J+1)`.

Thus define the continuing-branch supplied candidates:

```text
D_next = E, reindexed to Case2ResidualRowIndex(n,S,J+1)
                 by Case2ResidualColIndex(n,S,J+1),

C_next = C'_tail, reindexed to Case2ResidualColIndex(n,S,J+1).
```

Then the lower part of `D''' C'`, reindexed by the same row equivalence, is

```text
D_next C_next.
```

This is the finite product shape that a later source-coordinate transition
wrapper may use as supplied next residual/following-product data.  It is not
itself a proof that Aoyagi's chart construction produces all post-data.

## Lean target

Add a general block lemma:

```text
weightedPivotClearedBlock_mul_verticalBlock
```

Then add Case 2 displayed-paper names:

```text
case2DisplayedPostPivotResidualBlock
case2DisplayedPostPivotFollowingFactor
case2DisplayedPostPivotResidualBlock_nonempty_of_next
case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct
```

The last theorem should state that the lower rows of
`case2DisplayedPaperDppp * case2DisplayedPaperCprime`, after reindexing by
`case2DisplayedPivotRowComplementEquivResidualRowSucc`, equal
`case2DisplayedPostPivotResidualBlock *
case2DisplayedPostPivotFollowingFactor`.

## Kill conditions

- Do not identify `D_next` or `C_next` with chart-produced recurrence or
  exponent post-data.
- Do not claim chart coverage, atlas construction, transition invariance,
  coordinate regularity, Jacobian/volume arithmetic, normal crossings, or RLCT
  extraction.
- Do not use the terminal `(S+1,0)` relabel or the stopped-continuation
  absorption theorems here.
- Do not hide the fact that the top row `C'_0` has been split off; the theorem
  only packages the lower part of the product for the continuing branch.
