# Statement card - A4 selected-entry principalization and unit facts

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`6033ff3b39534bba755f4fd389684e008225a1f2`.

Names:

- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp_isUnit`
- `DLNFibre.DLN.Aoyagi.weightedPivotBlockRowOp_det_isUnit`
- `DLNFibre.DLN.Aoyagi.pivotQ_isUnit`
- `DLNFibre.DLN.Aoyagi.pivotQ_det_isUnit`
- `DLNFibre.DLN.Aoyagi.pivotQinv_isUnit`
- `DLNFibre.DLN.Aoyagi.pivotQinv_det_isUnit`
- `DLNFibre.DLN.Aoyagi.selectedEntryChartMap_centerIdeal_eq_span_singleton`
- `DLNFibre.DLN.Aoyagi.case2_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem`
- `DLNFibre.DLN.Aoyagi.case1_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem`

## Statement

Lean now records two elementary finite-algebra facts at the selected-entry
regularity boundary:

- the finite `P`, `Q`, and `Q^-1` matrices used in the pivot algebra are units,
  and their determinants are units;
- for any finite center and selected pivot in that center, the ideal generated
  by the transformed selected-entry center generators is exactly the principal
  ideal `(u)`.

The ideal statement has Case 1 and Case 2 specializations for
`case1CenterGenerators` and `case2ResidualBlockPivotEntries`.

## Source Role

This captures the elementary part of the blow-up chart story: in a selected
generator chart, the pullback of the finite center ideal is principal, generated
by the selected variable. It also records that the displayed finite row/column
operation matrices are invertible matrices.

## Proved

- `weightedPivotBlockRowOp q x`, `pivotQ y`, and `pivotQinv y` are matrix
  units.
- Their determinants are units.
- If `pivot ∈ center`, then
  `Ideal.span {selectedEntryChartMap pivot u residual i | i ∈ center}` equals
  `Ideal.span {u}`.
- The same principalization is available for the Case 2 residual-block center
  and the Case 1 finite center.

## Assumed

- The selected pivot belongs to the finite center.
- In the Case specializations, the finite centers are supplied as already
  defined in Lean.

## Not Proved

- No affine blow-up atlas or chart coverage.
- No claim that Aoyagi displays arbitrary non-top-left pivot charts.
- No source-order transition formula for non-displayed pivots.
- No chart-produced recurrence or exponent post-data.
- No polynomial-coordinate Jacobian formula or analytic germ-invariance result.
- No source comparability, normal crossings, or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-selected-entry-principalization-unit-facts-a4.md`.
- Reproduction check:
  `review-selected-entry-principalization-unit-facts-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From repository root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory: no Lean forbidden-token hits; matches are historical prose records
  of clean scans.
