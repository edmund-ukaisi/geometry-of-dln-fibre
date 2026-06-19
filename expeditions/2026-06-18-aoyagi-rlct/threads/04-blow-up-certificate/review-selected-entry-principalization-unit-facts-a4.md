# Review - A4 Selected-Entry Principalization and Unit Facts

Status: reviewed; no blockers found.

## Reviewers

- Source/math reviewer: `Lovelace the 3rd`.
- Lean/API reviewer: `Dalton the 3rd`.

## Source and Math Review

The source/math review found no blocker. The added facts stay inside
elementary finite algebra:

- `selectedEntryChartMap_centerIdeal_eq_span_singleton` proves the exact
  generator-image argument: the selected pivot contributes `u`, and every
  transformed center generator is divisible by `u`.
- The Case 1 and Case 2 specializations remain statements about a supplied
  pivot in a finite center.
- `weightedPivotBlockRowOp_isUnit`, `pivotQ_isUnit`, and `pivotQinv_isUnit`
  match the finite unitriangular matrix operations used in Aoyagi's displayed
  `P/Q` algebra.

The review emphasized that these determinant-unit facts are matrix facts, not
Jacobian or atlas facts.

## Lean and API Review

The Lean/API review found no correctness or robustness issue. Two low-level API
polish points were incorporated:

- the extra `Mathlib.RingTheory.Ideal.BigOperators` import was removed;
- the selected-entry ideal principalization theorems now use
  `[CommSemiring R]` rather than `[CommRing R]`.

## Required Caveats

- This is finite ideal algebra for a supplied selected-generator chart.
- This is not full principalization or resolution of the whole center.
- This is not affine blow-up atlas construction or chart coverage.
- The determinant-unit lemmas do not compute polynomial-coordinate Jacobians.
- The results do not produce recurrence post-data, exponent post-data,
  source-order transition formulas, normal crossings, or RLCT extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`: passed in review.
- Controller rerun:
  `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`: passed.
- Controller rerun: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- Controller rerun: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- Controller rerun: `git diff --check`: passed.
