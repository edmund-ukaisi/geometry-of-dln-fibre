# A4 Case 2 Successor Source Substitution Review

Date: 2026-06-19.

Scope: xhigh source/math and Lean/API review of the displayed Case 2
successor source-substitution handoff.

## Reviewers

- Source/math explorer: `Faraday the 2nd`.
- Lean/API explorer: `Turing the 2nd`.

## Verdict

No blockers. Both reviewers confirmed that the checkpoint is honest
conditional bookkeeping: it connects Aoyagi's displayed `D_J = uD'_J`
substitution to the recurrence update `b'_i = u b_i`, with the selected
variable counted once inside the supplied successor weights.

The Lean/API review confirmed that the old residual row index type is used only
to extract Nat row levels, while the supplied successor state is accessed
through Nat-indexed `post.weight`. The pivot rewrite through
`case2ResidualRowLevel_displayedPivotRow` and the lower-row rewrites through
`case2ResidualRowLevel_ge` are sound.

## Required Caveats

- This does not prove that the Case 2 blow-up chart produces the supplied
  post-state.
- This does not prove arbitrary-pivot chart coverage.
- This does not prove coordinate regularity/Jacobian facts.
- This does not prove exponent updates or a transition invariant.
- This does not prove source comparability.
- This does not repair the printed Case 2 vector mismatch.
- This does not introduce normal-crossing or RLCT extraction claims.

## Checks

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From worktree root: `git diff --check`: passed.
