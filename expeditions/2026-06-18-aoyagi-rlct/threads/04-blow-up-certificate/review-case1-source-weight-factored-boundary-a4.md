# Review - A4 Case 1 source-weight factored boundary

Status: reviewed; no blockers found.

## Reviewers

- Implementation reviewer: `Huygens the 3rd`.

## Math Review

The old-weight recurrence identification is correct.  The recurrence
`mulStepAt step u h` changes the factor at level `h`, so it first affects row
`h+1`.  Therefore rows with level `<= h` keep the factored-base weight, while
rows below the strip gain the factor `u`.

The canonical residual-row predicate

```text
case2ResidualRowLevel i <= J + J1
```

is the right upper boundary for the displayed Case 1(2) strip.  The lower
bound `J+1 <= case2ResidualRowLevel i` comes from the residual-row index type.
The complement is therefore the lower residual range beginning at
`J+J1+1`.

## Lean/API Review

The source-weight diagonal theorem correctly combines the recurrence rewrite
with `case1RowStrip_diagonal_mul_sourceMatrix`: strip rows get the common `u`
from the source matrix, and lower rows get it from the old selected factor in
the diagonal.

The added declarations remain finite source-weight algebra.  They do not
assert chart production, hidden old-label validity, or a full
pre-state-to-post-state transition.

One residual API note: the new declarations do not require `1 <= J1` or
`J+J1 <= prefixMinNat n S`.  This is correct for the algebraic identity, but
downstream use as the actual Case 1 row strip must still supply the Case 1
hypotheses.

## Caveats

- This is not a chart-production theorem.
- It does not construct the factored-base recurrence.
- It does not prove hidden old-label source validity.
- It does not prove post-data production, Jacobian accounting, normal
  crossings, or RLCT extraction.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From the worktree root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory found no Lean forbidden-token use; hits are existing prose
  mentions in expedition notes and statement cards.
