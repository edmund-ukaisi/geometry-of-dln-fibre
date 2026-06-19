# A4 Case 2 Recurrence-Weight Update Review

Date: 2026-06-19.

Scope: xhigh source and Lean/API review of the conditional Case 2
recurrence-weight update.

## Reviewers

- Source/pen-and-paper explorer: `Lagrange the 2nd`.
- Lean/API explorer: `Kant the 2nd`.
- Final source/math reviewer: `Dalton the 2nd`.
- Final Lean/API reviewer: `Zeno the 2nd`.

## Verdict

Both explorers recommended the same next target: a conditional
recurrence-weight update, not a full transition theorem. The source target is
the PDF pp. 20-21 line `b'_i = u b_i`, interpreted with the consistent
normalization that the selected variable is counted once inside the post
weights.

The final source/math and Lean/API reviews found no blockers. They confirmed
that the theorem is source-faithful as conditional recurrence bookkeeping, that
the finite-domain and finite-product lemmas are reusable, and that the
statement keeps chart production, comparability, exponent-vector repair,
normal crossings, and RLCT extraction outside the proved result.

## Required Caveats

- This does not prove that the Case 2 blow-up chart produces the supplied
  post-state.
- This does not prove the corrected prefix-minimum vector is printed in the
  source.
- This does not repair the printed Case 2 vector mismatch.
- This does not prove source comparability from the Case 2 gap.
- This does not count both `b'_i=u*b_i` and the standalone outside `u`.
- This is not chart coverage, Jacobian/regularity, exponent update,
  transition-invariant, termination, normal-crossing, or RLCT theorem.

## Checks

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From worktree root: `git diff --check`: passed.
