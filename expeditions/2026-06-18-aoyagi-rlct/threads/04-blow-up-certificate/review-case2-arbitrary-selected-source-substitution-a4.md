# A4 Case 2 Arbitrary Selected-Entry Source Substitution Review

Date: 2026-06-19.

Scope: xhigh source/math and Lean/API review of the arbitrary selected-entry
Case 2 source-substitution transport checkpoint.

## Reviewers

- Source/math explorer: `Hume the 3rd`.
- Lean/API explorer: `Planck the 3rd`.

## Source/Math Verdict

No blockers.

The source/math review confirmed that the row and column domains are separated
correctly: residual rows are `J+1..mu_S`, while residual columns use actual
width `J+1..n_(S+1)`. The selected-entry substitution and pivot-first
transport match the pen-and-paper derivation, and the chart-coverage caveats
are explicit.

One wording issue was incorporated: for an arbitrary pivot, the `Q/P`
divisibility condition is on every pivot-complement row after pivot-first
reindexing,

```text
u * weight rowPivot divides u * weight i
```

not on "lower" rows in the source's displayed top-left order.

## Lean/API Verdict

No blockers.

The Lean/API review confirmed that the theorem family is an honest finite
algebra kernel and that overclaiming risk is controlled by the docstrings and
statement shape. One usability fix was incorporated:
`case2ResidualBlockPivotOfMem_pair` records the paired source-coordinate
identity for row/column subtype pivots extracted from
`case2ResidualBlockPivotEntries`.

Two non-blocking API follow-ups remain:

- Basic `case2Selected...` definitions currently live in the later
  `CommRing` section, so they inherit a stronger typeclass than the underlying
  selected-entry matrix API needs.
- A future wrapper from `p : ℕ × ℕ`, `hp : p ∈ case2ResidualBlockPivotEntries`,
  and source-coordinate residual data could reduce friction for source-facing
  arbitrary-pivot statements.

## Required Caveats

- This is finite algebra for a supplied residual-block pivot.
- This does not prove affine blow-up atlas construction or chart coverage.
- This does not claim Aoyagi displays arbitrary non-top-left pivot charts.
- This does not prove chart regularity, Jacobian facts, recurrence post-state
  production, exponent updates, transition invariants, normal crossings, or
  RLCT extraction.

## Checks

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From worktree root: `git diff --check`: passed.
