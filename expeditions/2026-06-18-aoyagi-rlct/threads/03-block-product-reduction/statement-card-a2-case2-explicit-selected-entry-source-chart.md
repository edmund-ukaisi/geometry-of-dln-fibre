# Statement card - A2 Case 2 explicit selected-entry source chart

## Claim

The continuing Case 2 selected-entry coordinates define an explicit two-edge
retained-passive source family.  For every successor selected-entry coordinate
vector `yNext`, the constructed source family lies in the source-recursive
determinant chart and its actual source-readback residual-factor product is the
successor selected-entry matrix.

Nonzeroness is a separate corollary from `yNext` having nonzero displayed
successor pivot coordinate.

## Lean Target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean
lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Target names:

```lean
case2DisplayedPostPivotSourceResidualOfMatrix
case2DisplayedPostPivotFreeCprimeOfMatrix
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_sourceResidualOfMatrix_freeCprimeOfMatrix
case2SuccessorSelectedEntrySourceResidual
case2SuccessorSelectedEntrySourceCprime
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_successorSelectedEntrySource_eq
case2PostPivotSelectedEntryRetainedPassiveData
case2PostPivotSelectedEntrySourceEdgeFamily
case2PostPivotSelectedEntrySourceEdgeFamily_sourceRecursiveDetChart
case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix
```

## Proof Basis

The source residual is a zero extension of the target selected-entry matrix
reindexed to successor residual columns.  The free `Cprime` tail is the
matching reindexed identity.  Their displayed post-pivot product is therefore
the selected-entry target matrix.

Packaging those two factors as `case2PostPivotRetainedPassiveData` gives a
determinant-chart point.  The retained-passive source map sends it to
`sourceRecursiveDetChart`, and `sourceReadback_edgeMatrix_eq` identifies the
actual readback with the constructed datum.

## Nonclaims

This does not prove arbitrary retained-passive source/readback factor
alignment. It does not prove continuity, measurability, Jacobian or
source-prior pushforward, source-rank coverage, normal crossings, pole order,
or RLCT.

