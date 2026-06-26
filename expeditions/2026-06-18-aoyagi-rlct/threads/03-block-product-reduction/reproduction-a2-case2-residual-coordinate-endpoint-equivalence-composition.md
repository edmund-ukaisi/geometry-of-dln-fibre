# Reproduction - A2 Case 2 residual-coordinate endpoint-equivalence composition

Date: 2026-06-25.

Status: Lean target implemented as finite index bookkeeping.

## Source Boundary

Aoyagi p. 13 treats the residual scalar coordinates of a rectangular block as
the product of its residual row and column coordinate labels.  For the Case 2
center on pp. 19-22, the current residual row labels are

```text
J+1, ..., M(S)
```

and the current residual column labels are

```text
J+1, ..., M^(S+1).
```

The previous index result identifies the product

```text
AoyagiResidualBlockCoordinateIndex
  (Case2ResidualRowIndex n S J)
  (Case2ResidualColIndex n S J)
```

with the candidate selected-entry center

```text
case2ResidualBlockPivotEntries n S J.
```

The remaining fixed-base source question is not the product construction
itself.  It is whether the endpoint residual row and column complement types
are identified with the Case 2 residual row and column ranges.

## Calculation

Let

```text
rowEquiv : mu ~= Case2ResidualRowIndex n S J
colEquiv : nu ~= Case2ResidualColIndex n S J.
```

Then a scalar endpoint residual coordinate `(i,j) : mu x nu` first maps to

```text
(rowEquiv i, colEquiv j)
```

in the Case 2 residual row/column product.  Applying the existing product
center equivalence sends it to the candidate pivot entry with underlying
source pair

```text
((rowEquiv i).val, (colEquiv j).val).
```

The inverse takes a pivot entry back through the previous product-center
equivalence and then applies `rowEquiv.symm` and `colEquiv.symm` to the two
factors.  The inverse laws are the inverse laws of the two supplied endpoint
equivalences and the previous product-center equivalence.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualIndex.lean`:

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs
```

with projection lemmas:

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs_apply
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs_apply
```

The second theorem is the same construction with the row and column
equivalences oriented out of the Case 2 residual row and column types, matching
the orientation used by the Case 2 residual-factor product reindex bridge.

## Nonclaims

- The row and column endpoint equivalences are not constructed.
- No fixed-base source chart is produced.
- No compatible residual-factor family is constructed.
- No selected-entry product matrix identity is proved.
- No source/image equality, source-measure transport, normal crossings, pole
  order, or RLCT theorem is proved.
