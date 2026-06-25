# Statement Card - A2 selected-entry residual-factor constructor readout

## Claim

The fixed-base residual-factor product-coordinate constructor gives the
selected-entry pointwise residual-coordinate readout when its supplied
factor product, evaluated at the selected-entry chart point, is the
selected-entry coordinate matrix.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualFactorProduct_eq_matrix
```

## Inputs

- A supplied regular-coordinate family `uBase`.
- A supplied compatible residual-factor family `Cfac`.
- A supplied residual-index equivalence `residualCoordEquiv`.
- A supplied factor-product identity for
  `Cfac (SelectedEntrySignedBox.CenterCoord.chartMap pivot y)`.

## Boundaries

This is finite p.13 product-coordinate/readout algebra only.  It does not
construct `Cfac`, prove the factor-product selected-entry identity, construct
the residual-index equivalence, prove source/image equality, transport
measure, produce normal crossings, compute pole order, or prove RLCT.
