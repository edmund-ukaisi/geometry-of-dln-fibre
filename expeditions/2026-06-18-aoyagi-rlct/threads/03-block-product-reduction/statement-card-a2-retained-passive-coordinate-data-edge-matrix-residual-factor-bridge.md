# Statement card - A2 retained-passive coordinate-data edge-matrix residual-factor bridge

## Claim

If the fixed-base source edge matrices along a selected-entry source chart are
realized as the `edgeMatrix` of retained-passive coordinate data in the
determinant chart, then the retained-passive source-readback residual-factor
matrix identity reduces to the corresponding data-level identity for the
supplied coordinate data.

## Lean artifacts

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`,
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`

Expected theorems:

```lean
sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq

PaperEndpointFixedBaseRegularCoordinateSourceData.
  sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix

PaperEndpointFixedBaseRegularCoordinateSourceData.
  aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_retainedPassiveCoordinateData_edgeMatrix
```

## Proved inputs

- `RetainedPassiveNonredundantCoordinateData.sourceReadback_edgeMatrix_eq`
  recovers retained-passive coordinate data from its edge matrix on the
  determinant chart.
- `sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq`
  specializes that inverse theorem to the fixed-base p.13 edge-matrix family.
- The previous source-readback selected-entry theorem turns the resulting
  source-readback matrix identity into the selected-entry residual square-sum.

## Supplied inputs

- retained-passive coordinate data `retainedData y`;
- determinant-chart membership for each `retainedData y`;
- edge realization
  `fixedBaseEdgeMatrix(Cedge(sourceChart y)) = (retainedData y).edgeMatrix`;
- residual-coordinate equivalence to the selected center;
- data-level residual-factor matrix identity for `(retainedData y).C`.

## Nonclaims

No retained-passive source chart is constructed.  No Case 2 entrywise product
identity, source image equality, weighted pushforward proof, Jacobian/source-
density theorem, original-loss comparison, normal crossings, pole order, or
RLCT extraction is proved.
