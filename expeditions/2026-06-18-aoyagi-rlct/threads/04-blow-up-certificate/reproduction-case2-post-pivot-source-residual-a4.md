# Pen-and-paper reproduction - Case 2 post-pivot source residual

Status: controller-reproduced; xhigh review pending.

This note isolates a source-coordinate representative for the lower-right
block left after Aoyagi's displayed Case 2 pivot.  It is a zero-extension of
already-proved finite post-pivot data.  It does not construct successor chart
coordinates, recurrence or exponent post-data, a transition invariant,
normal crossings, pole order, or RLCT data.

## Source

Aoyagi PDF pp. 19-22, displayed Case 2:

- the residual block before pivoting has rows `J+1..M(S)` and columns
  `J+1..M^(S+1)`;
- the displayed pivot is `(J+1,J+1)`;
- after the `Q` column operation and `P` row operation, the lower-right block
  is `D - x*y`;
- in the continuing branch this lower-right block is treated as the next
  same-stage residual block at `(S,J+1)`.

Earlier Lean checkpoints already formalised the finite reindexing from the
old pivot complements to `Case2ResidualRowIndex n S (J+1)` and
`Case2ResidualColIndex n S (J+1)`.

## Reproduction

Write Aoyagi's pivot-first normalised block as

```text
D_chart = [1  y]
          [x  D].
```

After the paper's column operation and row clearing, the continuing lower
block is

```text
D_next = D - x*y.
```

The finite Lean object

```text
case2DisplayedPostPivotResidualBlock n hS hcont residual
```

is exactly this `D_next`, reindexed over the next same-stage residual row and
column domains.

To view the same data as source-coordinate residual data, define a total
function on source pairs by

```text
R_next_source(i,j) =
  D_next(i,j),  if i in J+2..M(S) and j in J+2..M^(S+1),
  0,            otherwise.
```

Equivalently, in Lean membership language, the nonzero branch requires

```text
i in case2ResidualBlockRows n S (J+1)
j in case2ResidualBlockCols n S (J+1).
```

Restricting this total function by `case2SourceResidualBlock` at `(S,J+1)`
uses only source pairs already in those two finite sets.  Thus the membership
tests are discharged by the row and column subtype witnesses, and the
restriction recovers `D_next` entrywise.

The existing lower-row product identity can then be rewritten as

```text
(D''' * C')_tail =
  case2SourceResidualBlock R_next_source *
    case2SourceFollowingFactor (J := J+1) C.
```

This rewrite is only a notation adapter.  The zero extension chooses arbitrary
outside-block values, so it cannot be read as source production of the next
chart data.

## Lean target

Add:

```text
case2DisplayedPostPivotSourceResidual
case2SourceResidualBlock_postPivotSourceResidual
case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_sourceFollowingFactor
```

The first name is the zero-extended source representative.  The second proves
restriction recovery.  The third combines restriction recovery with the
existing source-following lower-row product.

## Kill conditions

- Do not claim that the zero extension is canonical outside the next residual
  block.
- Do not claim chart production, source-produced successor recurrence or
  exponent data, successor chart-family construction, or transition
  invariance.
- Do not identify this with a full source-produced next `C'^(S+1)`.
- Do not attach chart coverage, arbitrary pivot coverage, coordinate
  regularity, Jacobian arithmetic, normal crossings, pole order, RLCT
  extraction, terminal relabeling, or printed-vector repair.
