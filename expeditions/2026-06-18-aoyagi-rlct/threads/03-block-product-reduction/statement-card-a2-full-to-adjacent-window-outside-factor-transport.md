# Statement card - A2 full-to-adjacent-window outside-factor transport

## Claim

A longer residual-factor product can be split through a chosen adjacent
two-edge window.  If the adjacent middle product is identified with a supplied
matrix, then the full product has that matrix as the middle factor while the
left and right outside products remain explicit.

For the Case 2 selected-entry bridge, the supplied adjacent-window readout can
therefore be substituted only in the middle factor of a full product.

## Lean Artifacts

Files:

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean
```

Theorems:

```lean
ChartLocalSuffixState.residualFactorProduct_split_adjacent_two

ChartLocalSuffixState.residualFactorProduct_split_adjacent_two_of_middle_eq

residualFactorProduct_split_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
```

## Proved Inputs

- Generic residual-factor product transitivity:
  `ChartLocalSuffixState.residualFactorProduct_trans`.
- Existing adjacent Case 2 selected-entry readout:
  `residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`.

## Supplied Inputs

- A longer residual-factor family `C`.
- Endpoints `i,j` and adjacent window index `p` with
  `i <= p`, `p+2 <= j`.
- For the Case 2 specialization: endpoint equivalences, two displayed factor
  identities, and the entrywise successor selected-entry readout.

## Nonclaims

No outside factor is proved to be an identity, invertible, absorbed by a chart,
or irrelevant for the loss.  No full fixed-base suffix is identified with the
adjacent Case 2 window.  No endpoint equivalence, source chart, pivot nonzero
condition, source image, pushforward, Jacobian theorem, original-loss
comparison, normal crossings, pole order, or RLCT extraction is proved.
