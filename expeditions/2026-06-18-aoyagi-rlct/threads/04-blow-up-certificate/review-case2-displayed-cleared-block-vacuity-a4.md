# Review - A4 Case 2 Displayed Cleared-Block Vacuity

## Reviewers

- Source/math reviewer: `Laplace the 4th`, xhigh.
- Lean/API reviewer: `Arendt the 4th`, xhigh.

## Findings

No source/math fidelity defect was found.  The source reviewer confirmed that
the theorem is faithful as a tiny finite pivot-first lower-right vacuity
corollary: it uses the displayed pivot-complement matrix-vacuity theorem to
show that the lower-right argument of `weightedPivotClearedBlock` is zero when
the displayed pivot is valid and the next continuation bound fails.

No Lean/API defect was found.  The theorem is placed immediately after
`case2DisplayedNormalizedMatrix`, before substitution and following-factor
APIs it does not depend on.  The `let row/col/A` shape keeps the dependent
pivot-complement types readable, and the proof dependency is exactly
`case2DisplayedPivotComplement_matrix_eq_zero_of_not_next_cont`.

The name `case2DisplayedClearedBlock_eq_pivotOnly_of_not_next_cont` was kept.
Both reviewers flagged that the caveat fence is important: this is not
Aoyagi's full terminal branch, does not choose the exhausted side, does not
construct `D'''_J` from the whole source block, and does not build
`C'^(S+1)` or the `S+1` inductive transition.

## Verification

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`

## Residual Risk

This checkpoint proves only pivot-first lower-right cleared-block vacuity.
It does not construct Aoyagi's full terminal `D'''_J` branch, choose the
row/column terminal presentation, construct `C'^(S+1)`, build the `S+1`
recurrence/exponent state, prove chart coverage, coordinate regularity,
Jacobian arithmetic, normal crossings, RLCT extraction, termination,
transition invariance, or repair the printed Case 2 vector mismatch.
