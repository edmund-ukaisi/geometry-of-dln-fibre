# Statement card - A2 selected-entry residual-product square-sum

## Declaration

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.
  aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_residualProduct_eq_matrix
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean
```

## Statement

Given a finite equivalence between fixed-base residual coordinates and the
selected-entry center, if the fixed-base suffix residual product at
`CenterCoord.chartMap pivot y` is the selected-entry chart matrix, then the
fixed-base residual coordinate square-sum equals the selected-entry residual:

```text
aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap ... (chartMap pivot y))
= CenterCoord.residual pivot y.
```

## Role

This sharpens the scalar residual square-sum socket used by selected-entry
local-source/original-loss endpoints.  Future source-chart calculations may
supply a residual-product matrix identity rather than a raw scalar
square-sum identity.

## Boundary

This is API composition only.  It does not construct the source chart,
prove the residual-product matrix identity, construct the residual-index
equivalence, prove source coverage, identify source measures, produce normal
crossings, compute pole order, or prove RLCT.
