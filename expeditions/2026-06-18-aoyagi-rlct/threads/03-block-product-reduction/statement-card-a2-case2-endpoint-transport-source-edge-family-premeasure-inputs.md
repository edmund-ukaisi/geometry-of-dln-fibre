# Statement card - A2 Case 2 endpoint-transport source-edge-family pre-measure inputs

## Claim

For the two-edge Case 2 window, if endpoint equivalences identify the displayed
Case 2 endpoint family with the fixed-base retained-passive endpoint family,
then the source edge-family built from the endpoint-transported explicit Case 2
retained-passive datum lies in the fixed-base p.13 local source and has the
expected source-readback selected-entry residual-factor matrix readout.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Target name:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Proof Basis

Instantiate the fixed-base source-edge-family pre-measure specialization with
`M := 1` and with `retainedData yNext` equal to the endpoint transport of
`case2PostPivotSelectedEntryRetainedPassiveData`.  The determinant-chart input
is `case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart`,
and the stored residual-factor input is
`case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`.

## Nonclaims

This theorem does not construct the endpoint equivalences, prove their geometric
origin, transport `edgeMatrix` or `sourceReadback` as standalone operations,
prove a measure pushforward, compare Jacobians, prove positivity or
integrability, produce normal crossings, compute pole order, or extract RLCT.

## Status

Sorry-free, focused build passed, and reviewed PASS by xhigh `Mill` in
`review-a2-case2-endpoint-transport-source-edge-family-premeasure-inputs.md`.
