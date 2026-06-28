# Reproduction - A2 Case 2 source-readback selected-entry center-matrix handoff

Date: 2026-06-28.

Status: reproduced; Lean target selected.

## Target

The selected-entry local-measure consumers use an `hfactor` whose right-hand
side is written as a selected-entry center-coordinate matrix:

```text
AoyagiResidualBlockCoordinateIndex.matrix
  (c |-> SelectedEntrySignedBox.CenterCoord.chartMap pivot y
          (residualCoordEquiv c)).
```

The explicit Case 2 source family already proves that the actual
`sourceReadback` residual-factor product is the successor selected-entry
matrix.  This rung only unfolds that successor matrix into the consumer shape.

## Calculation

For the continuing Case 2 branch, the selected pivot is

```text
pivotNext = (J+2, J+2)
```

as an element of `case2ResidualBlockPivotEntries n S (J+1)`.  The successor
selected-entry matrix is definitionally

```text
case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext
= AoyagiResidualBlockCoordinateIndex.matrix
    (c |->
      SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
        (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
          n S (J+1) (Equiv.refl _) eNext c)).
```

The already-proved source-readback theorem gives

```text
residualFactorProduct (sourceReadback E(yNext)).C (Fin.last 2) 0
  = case2SuccessorSelectedEntryMatrix n hS hnext yNext eNext.
```

Unfolding the definition of `case2SuccessorSelectedEntryMatrix` gives the exact
selected-entry center-coordinate matrix shape expected by the local-measure
handoff.

Lean endpoint:

```text
case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** A content-named rewrite of the explicit
source-readback product equality into the selected-entry center-coordinate
matrix shape.

**Assumed.** The same finite branch data as the existing explicit Case 2 source
family: `hS`, `hcont`, `hnext`, `yNext`, `eNext`, and endpoint finite
typeclass data.

**Cited.** None.

**Deferred.** Applying this theorem to a fixed-base retained-passive local
source, proving source-prior pushforward, chart-image membership, Jacobian
density comparison, arbitrary retained-passive coverage, source-rank coverage,
normal crossings, pole order, and RLCT.

