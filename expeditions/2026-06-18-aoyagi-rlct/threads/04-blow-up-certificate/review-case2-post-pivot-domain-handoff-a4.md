# Review - A4 Case 2 post-pivot domain handoff

Reviewer: `Hubble the 5th` (xhigh pen-and-paper check).

Verdict: pass.

## Scope Checked

- Reproduction note:
  `reproduction-case2-post-pivot-domain-handoff-a4.md`.
- Aoyagi PDF pp. 19-22.
- Existing Lean definitions around `case2ResidualBlockRows`,
  `case2ResidualBlockCols`, `case2ResidualBlockPivotEntries`,
  `case2PostPivotRows`, `case2PostPivotCols`, and
  `case2PostPivotEntries`.

## Findings

No required changes.

The off-by-one convention is correct: Aoyagi's Case 2 residual block is
`J+1..M(S)` by `J+1..M^(S+1)`, and after selecting the displayed pivot
`(J+1,J+1)` the lower-right block begins at `J+2`.

The handoff is same-stage `(S,J+1)`, not the terminal `(S+1,0)` relabel.
Aoyagi distinguishes the continuing branch where `J` increases from the
exhausted branch where `S` increases.

The proposed finite-set equalities are definitional after unfolding, and the
nonemptiness wrapper is consistent with the existing theorem
`case2PostPivotEntries_nonempty_iff_next_cont`.  The reviewer notes that
`hS : 1 <= S` must remain on any theorem using the prefix-minimum recurrence.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

## Landed-patch review

Reviewer: `Dirac the 5th` (xhigh landed-patch review).

Verdict: pass, with one low-severity documentation note incorporated.

No mathematical or Lean fidelity issues were found.  The reviewer checked that
the post-pivot domains unfold to the next same-stage residual domains, the
off-by-one convention is correct, and `hS : 1 <= S` remains on the theorem
using the prefix-minimum recurrence.

The incorporated note was that the pivot-complement equivalence APIs also
carry `hS` and current continuation `hcont` because their source subtypes are
defined from the displayed current pivot, not because the target domain handoff
itself needs extra source production.
