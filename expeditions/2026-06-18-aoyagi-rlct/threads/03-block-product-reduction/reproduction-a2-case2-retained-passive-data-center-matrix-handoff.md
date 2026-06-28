# Reproduction - A2 Case 2 retained-passive data center-matrix handoff

Date: 2026-06-28.

Status: reproduced; Lean target selected and proved.

## Target

The previous handoff exposed the actual source-readback product of the explicit
Case 2 selected-entry source family:

```text
residualFactorProduct (sourceReadback (edgeMatrix data)).C
  = selected-entry center-coordinate matrix.
```

For canonical retained-passive chart-side consumers, the natural hypothesis is
instead on the stored retained-passive coordinate datum:

```text
residualFactorProduct data.C
  = selected-entry center-coordinate matrix.
```

This rung removes only the `sourceReadback (edgeMatrix data)` wrapper for the
explicit constructed datum.

## Calculation

The explicit selected-entry retained-passive datum is

```text
case2PostPivotSelectedEntryRetainedPassiveData
  = case2PostPivotRetainedPassiveData
      (case2SuccessorSelectedEntrySourceResidual yNext eNext)
      (case2SuccessorSelectedEntrySourceCprime yNext eNext).
```

Its active `C` fields are exactly the concrete two-edge factor family

```text
case2PostPivotFreeTwoEdgeFactorFamily
  (case2SuccessorSelectedEntrySourceResidual yNext eNext)
  (case2SuccessorSelectedEntrySourceCprime yNext eNext).
```

The existing finite product theorem gives

```text
residualFactorProduct
  (case2PostPivotFreeTwoEdgeFactorFamily
    (case2SuccessorSelectedEntrySourceResidual yNext eNext)
    (case2SuccessorSelectedEntrySourceCprime yNext eNext))
  (Fin.last 2) 0
  = case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext.
```

Unfolding `case2SuccessorSelectedEntryMatrix` gives the selected-entry
center-coordinate matrix with displayed successor pivot `(J+2,J+2)`:

```text
AoyagiResidualBlockCoordinateIndex.matrix
  (fun c =>
    SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
      (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J+1) (Equiv.refl _) eNext c)).
```

Therefore the stored retained-passive datum's `C` product already has the exact
matrix shape required by chart-side residual readout consumers.

Lean endpoint:

```text
case2PostPivotSelectedEntryRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** The explicit Case 2 selected-entry
retained-passive datum's stored `C` residual-factor product equals the
successor selected-entry center-coordinate matrix.

**Assumed.** The same finite branch data as the explicit Case 2 source family:
`hS`, `hcont`, `hnext`, `yNext`, `eNext`, and endpoint finite typeclass data
for the free endpoint.

**Cited.** None.

**Deferred.** Endpoint transport from
`case2PostPivotTwoEdgeDomain n S J τ` to a fixed-base
`throughSubspaceEndpointComplementIndex` suffix; fixed-base local-source
membership; source-prior pushforward; chart-image membership; Jacobian density
comparison; arbitrary retained-passive coverage; source-rank coverage; normal
crossings; pole order; and RLCT.
