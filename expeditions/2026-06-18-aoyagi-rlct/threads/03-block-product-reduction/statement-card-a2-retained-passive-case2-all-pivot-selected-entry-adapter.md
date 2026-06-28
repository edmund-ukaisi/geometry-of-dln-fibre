# Statement card - A2 retained-passive Case 2 all-pivot selected-entry adapter

## Claim

For a displayed Case 2 post-pivot two-edge product matrix, nonzeroness of the
whole displayed product is enough to choose some selected-entry pivot and
selected-entry coordinates.  Consequently, the generic retained-passive
two-edge residual-factor product, the two-edge `ofTopologyTuple` specialization,
and the canonical p.13 chart-side square-sum admit selected-entry coordinates
after the supplied displayed factor identities.

## Lean artifacts

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

New theorems:

```lean
exists_pivot_residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero

exists_pivot_residualFactorProduct_ofTopologyTuple_eq_selectedEntryCenter_matrix_of_case2PostPivot_of_ne_zero

PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_pivot_aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_case2PostPivot_of_ne_zero
```

## Inputs

- The two displayed factor identities `hD` and `hF`, identifying the stored
  retained-passive factors with Aoyagi's displayed post-pivot residual block
  and following factor after endpoint equivalences.
- A residual-coordinate equivalence to the finite selected-entry center.
- Nonzeroness of the displayed product matrix
  `case2DisplayedPostPivotFreeTwoEdgeFactorProduct ... != 0`.

## Proof basis

This uses the existing finite all-pivot selected-entry inverse
`SelectedEntrySignedBox.CenterCoord.exists_pivot_matrix_eq_chartMap_of_ne_zero`.
That theorem chooses a nonzero matrix entry as the selected pivot, transports
through `(Equiv.prodCongr e2 e0).trans residualCoordEquiv`, and supplies the
entrywise selected-entry chart readout consumed by the older Case 2 bridges.

No fresh Aoyagi source reproduction is required for this adapter: the finite
all-pivot calculation is already reproduced in
`reproduction-a2-selected-entry-all-pivot-nonzero-coverage.md` and reviewed in
`review-a2-selected-entry-all-pivot-nonzero-coverage.md`.

## Nonclaims

The theorem does not prove the displayed product matrix is nonzero.  It does
not prove actual retained-passive source/readback factor alignment, original
source-prior transport, normal crossings, pole order, or RLCT.
