# Statement card - A2 selected-entry residual-product matrix readout

## Lean Artifact

File: `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`.

Name:

- `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix`

## Statement

Lean now proves that a supplied fixed-base suffix residual-product matrix
identity implies the pointwise selected-entry coordinate readout used by the
selected-entry original-loss wrapper.

The hypothesis is a matrix equality:

```text
residualProduct(E(chartMap(pivot,y)))
  = matrix(c ↦ chartMap(pivot,y)_(residualCoordEquiv c)).
```

The conclusion is the coordinate readout:

```text
residualCoordinateMap(chartMap(pivot,y))_c
  = chartMap(pivot,y)_(residualCoordEquiv c).
```

## Proved

The proof combines:

- `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct`;
- the supplied residual-product matrix identity;
- `AoyagiResidualBlockCoordinateIndex.value_matrix`.

## Not Proved

No construction of `CedgeBase`, no proof of the residual-product matrix
identity, no construction of `residualCoordEquiv`, no source coverage,
source-measure transport, analytic Jacobian identity, normal crossings, pole
order, or RLCT.

## Reproduction

- `reproduction-a2-selected-entry-residual-product-matrix-readout.md`.

## Verification

- From `lean/`:
  `env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure`
