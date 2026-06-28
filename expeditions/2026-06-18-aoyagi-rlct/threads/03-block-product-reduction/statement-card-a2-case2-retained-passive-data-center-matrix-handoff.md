# Statement card - A2 Case 2 retained-passive data center-matrix handoff

## Claim

The explicit continuing Case 2 selected-entry retained-passive datum has stored
`C` residual-factor product equal to the selected-entry center-coordinate matrix
with displayed successor pivot `(J+2,J+2)`.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Target name:

```lean
case2PostPivotSelectedEntryRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

## Proof Basis

Unfold `case2PostPivotSelectedEntryRetainedPassiveData` and
`case2PostPivotRetainedPassiveData`, apply
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_successorSelectedEntrySource_eq`,
and unfold `case2SuccessorSelectedEntryMatrix`.

## Nonclaims

This is only a finite retained-passive datum equality.  It does not prove
fixed-base endpoint transport, local-source membership, source-prior
pushforward, chart-image membership, Jacobian density comparison, coverage,
normal crossings, pole order, or RLCT.
