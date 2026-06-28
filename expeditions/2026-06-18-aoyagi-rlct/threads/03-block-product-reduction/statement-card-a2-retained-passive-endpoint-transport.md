# Statement card - A2 retained-passive endpoint transport

## Claim

Endpoint equivalences transport explicit residual-factor products and the
stored `C` residual-factor product of retained-passive nonredundant coordinate
data.  Applied to the explicit Case 2 selected-entry datum, this gives the
same selected-entry center-coordinate matrix readout over any endpoint family
equivalent to `case2PostPivotTwoEdgeDomain`.

## Lean Targets

Files:

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Target names:

```lean
ChartLocalSuffixState.residualFactorProduct_endpointTransport
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.endpointTransport
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.endpointTransport_detChart
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.residualFactorProduct_C_endpointTransport
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

## Proof Basis

Prove the product transport by decreasing induction over the endpoint product.
The base case is `submatrix_one_equiv`; the step combines
`residualFactorProduct_castSucc` with `Matrix.submatrix_mul_equiv`.

Define retained-passive endpoint transport fieldwise.  The determinant-chart
predicate is unchanged because it only reads `Ctop` and `A1passive`; the stored
`C` product follows from the general product transport.  The Case 2 theorem
composes this with the existing selected-entry retained-passive datum readout.

## Nonclaims

This is finite endpoint algebra only.  It does not transport the retained-passive
`edgeMatrix`, `sourceRecursiveDetChart`, `sourceReadback`, or suffix-recursion
state.  It does not prove fixed-base source-chart realization, local-source
membership, measure transport, normal crossings, pole order, or RLCT.
