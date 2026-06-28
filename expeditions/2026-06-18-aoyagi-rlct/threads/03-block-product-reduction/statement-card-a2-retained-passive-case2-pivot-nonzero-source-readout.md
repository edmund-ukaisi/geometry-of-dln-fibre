# Statement card - A2 retained-passive Case 2 pivot-nonzero source readout

## Claim

For the displayed Case 2 post-pivot two-edge product, if the fixed successor
pivot coordinate `(J+2,J+2)` is nonzero after reindexing by
`eNext : tau ~= Case2ResidualColIndex n S (J+1)`, then there exist successor
selected-entry coordinates `yNext` whose source chart map agrees entrywise
with that product.  Consequently, the synthetic retained-passive two-edge
datum has the corresponding successor selected-entry residual-factor matrix.

## Lean artifacts

Files:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Definitions and theorems:

```lean
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
SelectedEntrySignedBox.CenterCoord.chartMap_preimageOfPivotNeZero
SelectedEntrySignedBox.CenterCoord.exists_chartMap_eq_value_of_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.exists_matrix_eq_chartMap_of_pivot_ne_zero

exists_successorSourceChartMap_entrywise_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero

exists_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_pivot_ne_zero
exists_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_pivot_ne_zero
exists_case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_pivot_ne_zero

exists_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_pivot_ne_zero
```

## Proved inputs

- Center-coordinate selected-entry chart map formula:
  pivot coordinate is unchanged and nonpivot coordinates are multiplied by the
  pivot coordinate.
- Matrix-level readout: a matrix with a nonzero selected pivot entry is a
  selected-entry chart matrix after any supplied residual-coordinate
  equivalence.
- Definitional bridge from `case2DisplayedSourceChartMap` to
  `SelectedEntrySignedBox.CenterCoord.chartMap`.
- Synthetic Case 2 retained-passive datum bridge from entrywise successor
  readout to the retained-passive residual-factor product matrix.
- Retained-passive two-edge `ofTopologyTuple` and canonical p.13 chart-side
  square-sum consumers of the same pivot-nonzero matrix inverse.

## Supplied inputs

- `hcont : J+1 <= prefixMinNat n (S+1)`;
- `hnext : J+2 <= prefixMinNat n (S+1)`;
- `eNext : tau ~= Case2ResidualColIndex n S (J+1)`;
- nonzero value of the displayed post-pivot two-edge product at the fixed
  successor pivot after reindexing.
- for the generic retained-passive and canonical variants: nonzero value of
  the displayed post-pivot product at the supplied selected pivot after the
  product-coordinate equivalence
  `(Equiv.prodCongr e2 e0).trans residualCoordEquiv`.

## Nonclaims

The fixed successor pivot nonzero condition is not proved.  No retained-
passive source chart, longer-suffix transport, source image coverage,
pushforward/Jacobian theorem, original-loss comparison, normal crossings, pole
order, or RLCT extraction is proved.
