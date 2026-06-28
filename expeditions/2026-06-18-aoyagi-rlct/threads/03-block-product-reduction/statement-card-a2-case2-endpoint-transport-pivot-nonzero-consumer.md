# Statement Card - A2 Case 2 endpoint-transport pivot nonzero consumer

## Claim

For the endpoint-transported explicit Case 2 selected-entry retained-passive
datum, the all-pivot selected-entry residual-product readout follows from the
successor pivot-coordinate nonzero hypothesis `hyNext`.

This removes the separate displayed-product nonzero hypothesis from the
explicit-datum consumer landed in the previous factor-alignment step.

## Source / Proof Basis

Aoyagi PDF pp. 19-22 for the continuing Case 2 selected-pivot construction and
successor selected-entry coordinates.  The Lean proof is finite matrix algebra:

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct_successorSelectedEntrySource_eq
case2SuccessorSelectedEntryMatrix_ne_zero_of_yNext_pivot_ne_zero
exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_ne_zero
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Expected declaration:

```text
exists_pivot_residualFactorProduct_case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_eq_selectedEntryCenter_matrix_of_yNext_pivot_ne_zero
```

The statement should still take the endpoint equivalences `e` and `eNext`, the
successor selected-entry coordinate vector `yNext`, and the residual-coordinate
equivalence.  It should replace `hprod` by the concrete pivot-coordinate
nonzero hypothesis `hyNext`.

## Nonclaims

No arbitrary `ofTopologyTuple` alignment, no arbitrary source-readback
provenance, no fixed-base endpoint provenance, no source-prior transport, no
Jacobian comparison, no normal crossings, no pole order, and no RLCT.

The conclusion is all-pivot/existential: it returns some selected-entry pivot
and coordinates.  It does not assert that the pivot is the successor pivot
`(J + 2, J + 2)` or that the produced coordinates are the supplied `yNext`.

## Verification Plan

Run the focused build for
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge`, then the
downstream Case 2 local Jacobian module, `scripts/sorries`, `git diff --check`,
touched-file marker search, direct axiom probe, and xhigh implementation
review.
