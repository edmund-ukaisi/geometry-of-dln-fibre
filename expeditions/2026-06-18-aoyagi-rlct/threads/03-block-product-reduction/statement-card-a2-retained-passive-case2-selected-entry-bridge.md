# Statement card - A2 retained-passive Case 2 selected-entry bridge

## Claim

For a two-edge retained-passive coordinate datum, the selected-entry
residual-factor matrix identity follows from the existing finite Case 2 product
bridge once the two retained-passive `C` factors are identified with Aoyagi's
displayed post-pivot residual block and following factor, and the displayed
post-pivot product is supplied entrywise as selected-center coordinates.

## Lean artifacts

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`

Theorems:

```lean
residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise

residualFactorProduct_retainedPassiveCoordinateData_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_entrywise
```

## Proved inputs

- `ChartLocalSuffixState.residualFactorProduct_fin_two_eq_mul` unfolds the
  two-edge product as `C 1 * C 0`.
- `residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`
  upgrades displayed Case 2 factor identities and an entrywise selected-center
  readout to the center-coordinate matrix identity.
- `residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`
  specializes the same bridge to Aoyagi's successor selected-entry chart-map
  vocabulary.

## Supplied inputs

- a two-edge retained-passive coordinate datum `data`;
- endpoint equivalences from the displayed Case 2 residual row, column, and
  free endpoint types to the retained-passive endpoint types;
- factor identities identifying `data.C 1` with the displayed post-pivot
  residual block and `data.C 0` with the displayed free following factor;
- the entrywise selected-center readout of the displayed post-pivot product.

## Nonclaims

No longer retained-passive suffix is sliced or transported to a two-edge chain.
No retained-passive coordinate datum is constructed.  No entrywise product
readout is proved from source construction.  No source chart, source image
equality, weighted pushforward, Jacobian/source-density theorem, original-loss
comparison, normal crossings, pole order, or RLCT extraction is proved.
