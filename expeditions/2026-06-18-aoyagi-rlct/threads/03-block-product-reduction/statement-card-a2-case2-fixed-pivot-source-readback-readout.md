# Statement Card - A2 Case 2 fixed-pivot source-readback readout

## Claim

For the endpoint-transported explicit Case 2 selected-entry datum, the
residual-factor product entry corresponding to the displayed successor pivot
`(J + 2, J + 2)` is exactly the supplied selected-entry coordinate
`yNext pivotNext`.  The same fixed-pivot readout holds for the fixed-base
source readback of the p.13 source edge family built from that datum.

## Source / Proof Basis

Aoyagi PDF pp. 19-22 for the Case 2 selected pivot and post-pivot
selected-entry source construction.  Lean dependencies:

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
AoyagiResidualBlockCoordinateIndex.value_matrix
SelectedEntrySignedBox.CenterCoord.chartMap_pivot
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_eq_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Lean Target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Expected declarations:

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_eq_yNext
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_fixedPivot_entry_ne_zero_of_yNext_pivot_ne_zero
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_residualFactorProduct_fixedPivot_entry_eq_yNext_of_case2EndpointTransport_sourceEdgeFamilyOfData
PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_residualFactorProduct_fixedPivot_entry_ne_zero_of_case2EndpointTransport_sourceEdgeFamilyOfData_yNext_pivot_ne_zero
```

## Nonclaims

No construction of `tau`, no proof of `hTau`, no canonical endpoint labelling,
no selected-entry label-preservation theorem for arbitrary noncanonical
endpoint equivalences, no arbitrary `ofTopologyTuple` alignment, no
source-prior transport, no Jacobian comparison, no normal crossings, no pole
order, and no RLCT.

## Verification Plan

Run focused builds of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`, then
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker search,
direct axiom probes for the new declarations, and xhigh review.
