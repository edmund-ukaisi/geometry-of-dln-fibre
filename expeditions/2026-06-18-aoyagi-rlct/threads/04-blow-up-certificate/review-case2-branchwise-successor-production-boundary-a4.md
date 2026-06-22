# Review - Case 2 Branchwise Successor Production Boundary

Date: 2026-06-22.

Reviewer: Socrates, xhigh effort.

Verdict: required fixes; addressed by controller patch.

## Required Fixes

1. Add the standing displayed-pivot hypotheses to the branch contract.  The
   actual-width and row-exhausted hypotheses alone do not justify the terminal
   prefix equality or pivot validity; existing Lean frontier data assumes
   `1 <= S`, `S <= L`, and `J+1 <= prefixMinNat n (S+1)`.
2. Clarify that the branch split is a Lean/A4 refinement of Aoyagi's printed
   branch sentence.  Aoyagi's non-strict guard lands at `(S,J+1)`, while the
   continuing payload here uses the stronger nonempty-next-center condition
   `J+2 <= prefixMinNat n (S+1)`.
3. State that the actual-width stopped and row-exhausted stopped hypotheses
   are not asserted to be mutually exclusive.

## Resolution

The reproduction, statement card, A4 thread, priorities, synthesis, and
theorem ledger were updated to make these three points explicit.

After these clarifications, the reviewer found the `Csucc` formula,
actual-width original-row collapse, row-exhausted transported-row boundary,
supplied-vs-produced separation, and kill conditions source-faithful and
consistent with the existing A4 Lean boundary.
