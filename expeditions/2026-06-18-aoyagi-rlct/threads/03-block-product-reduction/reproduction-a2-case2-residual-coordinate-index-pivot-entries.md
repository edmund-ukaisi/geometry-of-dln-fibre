# Reproduction - A2 Case 2 residual-coordinate index pivot entries

Date: 2026-06-25.

Status: Lean target implemented as finite index bookkeeping.

## Source Boundary

Aoyagi's Case 2 residual center on pp. 19-22 is the rectangular block with
rows

```text
J+1, ..., M(S)
```

and columns

```text
J+1, ..., M^(S+1).
```

The repo encodes these as `case2ResidualBlockRows n S J` and
`case2ResidualBlockCols n S J`.  Candidate selected entries in that center
are the product finite set

```text
case2ResidualBlockPivotEntries n S J
  = case2ResidualBlockRows n S J × case2ResidualBlockCols n S J.
```

Aoyagi p. 13's residual scalar-coordinate index for a rectangular residual
matrix is the product of row and column indices.  In Lean this is

```text
AoyagiResidualBlockCoordinateIndex μ ν = μ × ν.
```

Therefore the Case 2 residual scalar-coordinate index for the current block
is equivalent to the finite set of candidate pivot entries.

## Calculation

For

```text
i : Case2ResidualRowIndex n S J,
j : Case2ResidualColIndex n S J,
```

map the p.13 scalar residual coordinate `(i,j)` to the selected-entry center
element

```text
((i.val, j.val), membership proof).
```

The membership proof is exactly the row membership of `i` and column
membership of `j`, combined by the product-center definition.  The inverse
map takes a candidate entry `p` and extracts its row and column subtype
members with the existing `case2ResidualBlockPivotRowOfMem` and
`case2ResidualBlockPivotColOfMem`.

The two inverse laws are subtype extensionality plus the existing theorem
`case2ResidualBlockPivotOfMem_pair`.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualIndex.lean`:

```text
case2ResidualBlockCoordinateIndexEquivPivotEntries
```

It also provides simp projections for the forward map and inverse row/column
values.

## Nonclaims

- No selected-entry chart is constructed.
- No source/image equality or chart coverage is proved.
- No compatible residual-factor family is constructed.
- No selected-entry product matrix identity is proved.
- No source-measure transport, normal crossings, pole order, or RLCT theorem
  is proved.

