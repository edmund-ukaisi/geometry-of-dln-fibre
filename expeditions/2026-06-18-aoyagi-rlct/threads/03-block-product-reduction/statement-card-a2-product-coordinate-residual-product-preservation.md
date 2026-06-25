# Statement card - A2 product-coordinate residual-product preservation

## Declaration

```text
DLNFibre.DLN.Aoyagi.
  paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

## Statement

For the multi-edge p.13 product-coordinate matrix constructor,

```text
residualProduct
  (paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
    V Bv U0 u Ebase)
  last 0
=
residualProduct Ebase last 0.
```

The proof expands the constructor into the existing right/middle/left
product-coordinate edge patterns and applies the raw product-coordinate
residual-product preservation theorem.

## Role

This gives selected-entry readout work a clean residualProduct preservation
hook.  It records that the p.13 product-coordinate constructor preserves the
base suffix residual product instead of manufacturing an arbitrary terminal
residual matrix.

## Boundary

No source chart, no residual-index equivalence, no selected-entry matrix
identity, no source coverage, no measure transport, no normal crossings, no
pole order, and no RLCT.
