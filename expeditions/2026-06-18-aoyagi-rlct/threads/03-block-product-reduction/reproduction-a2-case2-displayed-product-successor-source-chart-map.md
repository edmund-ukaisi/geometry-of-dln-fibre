# Reproduction - A2 Case 2 displayed product successor source-chart map

Date: 2026-06-26.

Status: Lean target implemented as finite matrix extensionality.

## Source Boundary

Aoyagi pp. 19-22 support two separate pieces of notation:

- the old Case 2 selected-entry chart at stage `(S,J)`, with
  `d_(J+1,J+1)=u_(S,J+1)` and other old-center entries multiplied by
  `u_(S,J+1)`;
- the continuing post-pivot lower product `D_(J+1) * C'_+` on the next
  same-stage residual domains `(S,J+1)`.

This slice does not prove that the displayed lower product entries are
successor source-chart coordinates.  It records the finite bridge obtained
after that pointwise readout is supplied.

## Calculation

Let

```text
P = case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime.
```

Its row domain is `Case2ResidualRowIndex n S (J+1)` and its column domain is
`tau`.  Assume the continuing branch is strong enough to form the successor
center:

```text
hnext : J + 2 <= prefixMinNat n (S+1).
```

Let

```text
e0 : tau ~= Case2ResidualColIndex n S (J+1).
```

The already-proved endpoint product equivalence specializes to

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
  n S (J+1) (Equiv.refl _) e0
```

which sends a pair `(i,t)` to the concrete source-coordinate entry
`(i.1, (e0 t).1)` in `case2ResidualBlockPivotEntries n S (J+1)`.

Define the matrix

```text
M c =
  case2DisplayedSourceChartMap n hS hnext uNext residualNext
    ((case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J+1) (Equiv.refl _) e0 c).1).
```

If the pointwise successor source-chart readout is supplied,

```text
P i t = M (i,t),
```

then by the definition of `AoyagiResidualBlockCoordinateIndex.matrix`,

```text
AoyagiResidualBlockCoordinateIndex.matrix M i t = M (i,t) = P i t.
```

Thus `P` is exactly this successor source-chart-map matrix.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSourceChartMapMatrix_of_entrywise
```

## Nonclaims

- The successor source-chart pointwise readout is still supplied.
- The theorem does not prove the selected-center readout.
- The column endpoint equivalence is still supplied.
- No compatible residual-factor family is constructed.
- No source production of `Cprime`, successor `uNext`, or `residualNext` is
  proved.
- No source/image equality, source-measure transport, chart coverage,
  Jacobian theorem, normal crossings, pole order, or RLCT theorem is proved.
