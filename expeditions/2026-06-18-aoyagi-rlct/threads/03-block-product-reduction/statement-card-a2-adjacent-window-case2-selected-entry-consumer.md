# Statement card - A2 adjacent-window Case 2 selected-entry consumer

## Claim

An adjacent two-edge window in a longer supplied residual-factor family gives
the displayed Case 2 post-pivot product once the three endpoint equivalences
and the two factor identities are supplied.  If the displayed product has an
entrywise selected-entry readout, or if the fixed successor pivot nonzero
hypothesis supplies such a readout by the existing inverse theorem, then the
adjacent residual-factor product is the corresponding successor selected-entry
center-coordinate matrix.

## Lean artifacts

Files:

```text
lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean
lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Theorems:

```lean
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_adjacent_two_submatrix

residualFactorProduct_adjacent_two_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise

residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise

exists_residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero

exists_residualFactorProduct_retainedPassiveCoordinateData_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_pivot_ne_zero
```

## Proved inputs

- Generic adjacent two-edge residual-factor transport:
  `residualFactorProduct_adjacent_two_submatrix_eq_mul`.
- Case 2 displayed product identity:
  `case2DisplayedPostPivotFreeTwoEdgeFactorProduct`.
- Selected-entry center-coordinate matrix extensionality.
- Existing fixed-pivot selected-entry inverse for the displayed product.

## Supplied inputs

- Adjacent window index `p`.
- Endpoint equivalences for row, middle, and column endpoints.
- Factor identities identifying `C p.succ` with the post-pivot residual block
  and `C p.castSucc` with the following factor after reindexing.
- For the existential theorem, nonzero displayed product at the fixed
  successor pivot `(J+2,J+2)`.

## Nonclaims

No endpoint equivalence is constructed.  No full retained-passive suffix or
fixed-base endpoint product is collapsed to the adjacent window.  No Case 2
factor identity for a source-readback family is proved.  No pivot nonzero
condition, source chart, source image, pushforward, Jacobian theorem,
original-loss comparison, normal crossings, pole order, or RLCT extraction is
proved.
