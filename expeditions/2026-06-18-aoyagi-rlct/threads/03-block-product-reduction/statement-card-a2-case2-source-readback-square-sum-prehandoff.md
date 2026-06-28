# Statement card - A2 Case 2 source-readback square-sum prehandoff

## Claim

The square-sum of the explicit continuing Case 2 source family's actual
source-readback residual-factor product equals the selected-entry center
residual with displayed successor pivot `(J+2,J+2)`.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean
```

Target name:

```lean
aoyagiCoordinateSquareSum_case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenter_residual
```

## Proof Basis

Use
`case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix`,
read the matrix back with `AoyagiResidualBlockCoordinateIndex.value_matrix`,
reindex the square-sum by `aoyagiCoordinateSquareSum_comp_equiv`, and finish
with `SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap`.

## Nonclaims

This is only a finite source-readback square-sum calculation.  It does not prove
fixed-base endpoint transport, source-chart realization, local-source
membership, source-prior pushforward, chart-image membership, Jacobian density
comparison, coverage, normal crossings, pole order, or RLCT.
