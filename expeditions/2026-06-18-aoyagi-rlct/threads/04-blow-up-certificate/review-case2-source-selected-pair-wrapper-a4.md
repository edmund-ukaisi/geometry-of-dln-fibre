# Review - A4 Case 2 Source-Selected Pair Wrapper

Status: reviewed; no blockers found.

## Reviewers

- Source/math explorer: `Boyle the 3rd`.
- Lean/API explorer: `Erdos the 3rd`.

## Source and Math Review

The source/math review found that the safe statement is exactly a
reindexing/instantiation wrapper. Given `p : Nat × Nat` and
`hp : p ∈ case2ResidualBlockPivotEntries n S J`, the membership proof supplies
the source bounds

```text
J+1 <= p.1 <= prefixMinNat n S,
J+1 <= p.2 <= n (S+1).
```

The extracted row and column subtype pivots agree with the source coordinates
of `p`, and source-coordinate residual/following data are then restricted to
the residual row and column subtypes. Under the old Case 2 gap, flat old
residual-row weights apply to the selected row, not only to the displayed
`J+1` row. Under supplied post-data, successor weights rewrite
`u * pre.weight` at every residual row level.

No source/math blocker was found.

## Lean and API Review

The Lean/API review recommended a thin adapter layer plus wrappers around the
existing arbitrary selected-pivot theorems. The implemented API follows that
shape:

- `case2SourceResidualBlock`;
- `case2SourceFollowingFactor`;
- wrappers from source pivot membership to the old recurrence-gap `Q/P`
  theorem;
- wrappers from source pivot membership to the supplied-post-data
  successor-weight transport and `Q/P` theorem.

The implementation uses pair-valued source residual data
`Nat × Nat -> R`, matching the pivot-pair API already used for
`case2ResidualBlockPivotEntries`. The following factor is source-column
coordinate data `Nat -> τ -> R`.

The review warned against stating pivot-first objects directly in terms of
`p.1` and `p.2`; the implemented theorem statements keep the dependent
`pivotComplement` types in terms of the extracted subtype pivots.

## Required Caveats

- This is finite algebra for a supplied source pivot pair.
- This does not prove chart coverage.
- This does not claim Aoyagi displays arbitrary non-top-left Case 2 pivot
  charts.
- This does not prove a source-order transition formula for non-displayed
  pivots.
- This does not prove chart-produced post-data.
- This does not prove affine blow-up atlas construction, chart regularity,
  Jacobian facts, exponent transition invariants, normal crossings, or RLCT
  extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`: passed.
- `lake build DLNFibre`: passed, with only pre-existing Core warnings.
- `./scripts/sorries`: `0 sorry`, `0 #exit`, `0 native_decide`, `0 axiom`.
- `git diff --check`: passed.
