# Statement card - A2 Case 2 source-readback selected-entry center-matrix handoff

## Claim

The explicit continuing Case 2 source family's actual source-readback
residual-factor product is equal to the selected-entry center-coordinate matrix
with the displayed successor pivot `(J+2,J+2)`.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Target name:

```lean
case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

## Proof Basis

Use the existing theorem
`case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix`
and unfold `case2SuccessorSelectedEntryMatrix`.

## Nonclaims

This is only an exact-shape finite readback equality.  It does not prove a
local-measure theorem, source-prior pushforward, chart-image membership,
Jacobian density comparison, coverage, normal crossings, pole order, or RLCT.

