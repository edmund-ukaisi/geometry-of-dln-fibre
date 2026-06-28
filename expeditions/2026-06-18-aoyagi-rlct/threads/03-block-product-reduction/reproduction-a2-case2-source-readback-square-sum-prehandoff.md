# Reproduction - A2 Case 2 source-readback square-sum prehandoff

Date: 2026-06-28.

Status: reproduced; Lean target selected and proved.

## Target

The source-readback center-matrix theorem gives

```text
residualFactorProduct (sourceReadback E(yNext)).C
  = AoyagiResidualBlockCoordinateIndex.matrix
      (fun c => CenterCoord.chartMap pivotNext yNext (coordEquiv c)).
```

This rung reads out the square-sum of that matrix.  It is a pre-handoff
calculation: it does not identify `E(yNext)` with any fixed-base p.13 source
chart.

## Calculation

Let

```text
pivotNext = (J+2,J+2)
coordEquiv =
  case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    n S (J+1) (Equiv.refl _) eNext.
```

The existing source-readback equality gives

```text
P :=
residualFactorProduct (sourceReadback E(yNext)).C (Fin.last 2) 0
= AoyagiResidualBlockCoordinateIndex.matrix
    (fun c => CenterCoord.chartMap pivotNext yNext (coordEquiv c)).
```

Applying `AoyagiResidualBlockCoordinateIndex.value` and the value/matrix inverse
identity gives the coordinate function

```text
value P =
fun c => CenterCoord.chartMap pivotNext yNext (coordEquiv c).
```

Square-summing and reindexing along `coordEquiv` gives

```text
aoyagiCoordinateSquareSum (value P)
  = aoyagiCoordinateSquareSum (CenterCoord.chartMap pivotNext yNext).
```

By the selected-entry center-coordinate identity,

```text
aoyagiCoordinateSquareSum (CenterCoord.chartMap pivotNext yNext)
  = CenterCoord.residual pivotNext yNext.
```

Lean endpoint:

```text
aoyagiCoordinateSquareSum_case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenter_residual
```

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** The square-sum of the explicit Case 2
source-readback residual-factor product equals the selected-entry center
residual at the displayed successor pivot.

**Assumed.** The same finite branch data as the explicit Case 2 source family:
`hS`, `hcont`, `hnext`, `yNext`, `eNext`, and endpoint finite typeclass data.

**Cited.** None.

**Deferred.** Fixed-base endpoint transport and source-chart realization;
fixed-base local-source membership; source-prior pushforward; chart-image
membership; Jacobian density comparison; arbitrary retained-passive coverage;
source-rank coverage; normal crossings; pole order; and RLCT.
