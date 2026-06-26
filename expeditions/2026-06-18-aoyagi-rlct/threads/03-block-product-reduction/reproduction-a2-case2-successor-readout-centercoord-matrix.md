# Reproduction - A2 Case 2 successor readout CenterCoord matrix

Date: 2026-06-26.

Status: Lean target implemented as conditional composition.

## Source Boundary

Aoyagi pp. 19-22 support the displayed post-pivot product

```text
D_(J+1) * C'_+
```

on the continuing `(S,J+1)` domains.  They do not prove that entries of this
product are successor selected-entry chart coordinates.  This slice keeps the
successor entrywise readout as an explicit hypothesis and only changes the
target vocabulary from `case2DisplayedSourceChartMap` to
`SelectedEntrySignedBox.CenterCoord.chartMap`.

## Calculation

Assume the continuing branch has a successor center

```text
case2ResidualBlockPivotEntries n S (J+1)
```

and displayed successor pivot `(J+2,J+2)`.  Let

```text
yNext : case2ResidualBlockPivotEntries n S (J+1) -> real.
```

The supplied entrywise source-chart readout has the form

```text
P i t =
  case2DisplayedSourceChartMap n hS hnext
    (yNext pivotNext)
    (SelectedEntrySignedBox.CenterCoord.sourceResidual yNext)
    (residualIndex(i,t)).
```

By the definitional alignment already proved for the displayed Case 2 chart,
this right-hand side is

```text
SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
  (residualIndex(i,t)).
```

The previous residual-factor product bridge then upgrades the reindexed
displayed product equality to the unreindexed two-edge residual-factor product
matrix:

```text
ChartLocalSuffixState.residualFactorProduct C last 0 =
  AoyagiResidualBlockCoordinateIndex.matrix
    (fun c => SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
      (residualCoordEquiv c)).
```

The residual-coordinate equivalence is assembled from the supplied row
endpoint equivalence `e2`, the supplied target endpoint equivalence `e0k`,
and the supplied displayed-column-to-successor-column equivalence `eNext`.

## Lean Target

Implemented in
`lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean`:

```text
residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
```

## Nonclaims

- The successor entrywise readout is still supplied.
- The endpoint equivalences are still supplied.
- No compatible residual-factor family is constructed.
- No source production of `Cprime`, `yNext`, or successor source data is
  proved.
- No source/image equality, source-measure transport, chart coverage,
  Jacobian theorem, normal crossings, pole order, or RLCT theorem is proved.
