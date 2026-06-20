# Review - A4 Case 2 Displayed Pivot-Complement Exhaustion

## Reviewers

- Source/math fidelity reviewer: `Archimedes the 4th`, xhigh.
- Lean/API reviewer: `Lorentz the 4th`, xhigh.

## Findings

No source/math fidelity defect was found.  The source reviewer confirmed that
the row and column domains remain faithful to Aoyagi's displayed Case 2
calculation: rows are the prefix-minimum residual rows `J+2..M(S)`, columns
are the actual-width residual columns `J+2..M^(S+1)`, and the next
continuation condition is the old-notation bound `J+2 <= M(S+1)`.

The source reviewer requested one documentation caveat, now recorded in the
reproduction and statement card: these declarations are not Aoyagi's full
terminal matrix-shape theorem `D'''_J = (1,0,...,0)` or its transpose.  They
prove only that, after deleting the displayed pivot row/column, one
complement index type is empty when the next continuation bound fails.

The Lean/API reviewer found no soundness blocker.  One medium downstream API
issue was acted on: the checkpoint now includes
`case2DisplayedPivotComplement_matrix_subsingleton_of_not_next_cont` and
`case2DisplayedPivotComplement_matrix_eq_zero_of_not_next_cont`, so later
terminal-block work can use a matrix-level lower-right vacuity theorem instead
of repeatedly unpacking the empty row/column disjunction.

Two low/nit API suggestions were also acted on: the equivalences now have
small `[simp]` raw-value lemmas, and the row/column complement emptiness has
`iff` wrappers against the corresponding post-pivot subtype emptiness.

## Verification

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`

## Residual Risk

This checkpoint still stops before the matrix-shape theorem.  It does not
construct `D'''_J`, prove the whole post-`Q/P` zero pattern, choose or cover a
terminal chart branch, construct `C'^(S+1)`, build the `S+1` recurrence or
exponent state, compute Jacobians, prove normal crossings, extract RLCT,
prove termination, prove transition invariance, or repair the printed Case 2
vector mismatch.
