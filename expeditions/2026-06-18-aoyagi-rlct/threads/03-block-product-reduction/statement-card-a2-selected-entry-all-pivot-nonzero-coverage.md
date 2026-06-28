# Statement card: A2 selected-entry all-pivot nonzero coverage

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

## New names

```text
SelectedEntrySignedBox.CenterCoord.exists_pivot_chartMap_eq_value_of_ne_zero
SelectedEntrySignedBox.CenterCoord.exists_pivot_matrix_eq_chartMap_of_ne_zero
```

## Content

The first theorem says that any nonzero center-coordinate vector lies in the
image of some selected-entry chart:

```text
value != 0 ->
  exists pivot : center, exists y : center -> R,
    chartMap pivot y = value.
```

The second theorem transports this to residual matrices through a supplied
residual-coordinate equivalence:

```text
D != 0 ->
  exists pivot : center, exists y : center -> R,
    D =
      AoyagiResidualBlockCoordinateIndex.matrix
        (fun c => chartMap pivot y (residualCoordEquiv c)).
```

## Proof idea

For the center-coordinate theorem, `value != 0` gives a coordinate `pivot` with
`value pivot != 0`; apply the existing fixed-pivot inverse
`exists_chartMap_eq_value_of_pivot_ne_zero`.

For the matrix theorem, `D != 0` gives a nonzero matrix entry `(i,j)`.  Use
`residualCoordEquiv (i,j)` as the pivot and apply the existing fixed-pivot
matrix inverse
`exists_matrix_eq_chartMap_of_pivot_ne_zero`.

## Nonclaims

This is finite selected-entry chart coverage on the nonzero locus.  It does
not prove that retained-passive source/readback data land in a nonzero residual
matrix, does not identify Aoyagi's displayed post-pivot and following factors,
does not prove measure/prior transport, normal crossings, pole order, or RLCT.
