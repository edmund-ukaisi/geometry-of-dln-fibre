# Review - A4 Displayed Top-Left Source-Order Adapter

Status: reviewed; no blockers found.

## Reviewers

- Source-order scout: `Carver the 3rd`.
- Lean/API scout: `Hypatia the 3rd`.
- Pen-and-paper scout: `Peirce the 3rd`.
- Implementation reviewer: `Godel the 3rd`.

## Source and Math Review

The source-order review found that Aoyagi displays only the top-left
selected-entry chart `d_(J+1,J+1)` in Case 1(2) and Case 2. The common finite
calculation is the normalised `Q/P` block algebra after the selected chart has
already produced a pivot entry equal to `1`.

The pen-and-paper review reproduced the same calculation:

```text
A = [1 y; x D],
A Q = [1 0; x D-x*y],
P diag(b) (A Q) = diag(b) [1 0; 0 D-x*y],
C' = Q^-1 C.
```

Both reviews flagged the same caveat: Case 1(2) divides only the row strip and
also transforms the hidden old exceptional variable. It must not be treated as
a full residual-block selected-entry substitution.

## Lean and API Review

The Lean/API scout recommended a generic already-substituted pivot-first
interface rather than a full transition theorem. The implemented
`WeightedPivotFirstSubstitutionData` follows that shape: the weighted source
block and its equality with the normalised pivot block are supplied fields,
and the theorem only invokes existing finite `Q/P` algebra.

The small Case 1 helper
`Case1FirstJumpHypotheses.continuationBound_of_colBound` is finite width
bookkeeping. It uses first-jump row boundedness plus the actual column bound to
show `J+1 <= prefixMinNat n (S+1)`.

An independent implementation review found no blockers. It confirmed that
`WeightedPivotFirstSubstitutionData` packages only supplied weighted
pivot-first data and quotient witnesses, and that `sourceOrder_identity`
rewrites by `source_eq` before invoking the existing finite `Q/P` theorem.
The phrase "source-order adapter" should be read as an adapter for an already
supplied source-substituted block in pivot-first coordinates.

## Required Caveats

- This is not a Case 1 or Case 2 transition theorem.
- This does not construct the selected chart or prove atlas coverage.
- This does not prove chart regularity, transition regularity, or Jacobian
  behavior.
- This does not produce recurrence or exponent post-data.
- This does not resolve the Case 2 printed-vector mismatch.
- This does not supply the hidden old-label semantics in Case 1(2).
- This keeps the selected variable counted once in row weights, but assumes the
  supplied weighted source block has already made that normalization choice.

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
