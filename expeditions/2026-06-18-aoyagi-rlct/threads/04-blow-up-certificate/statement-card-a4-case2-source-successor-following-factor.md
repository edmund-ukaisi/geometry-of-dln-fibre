# Statement card - A4 Case 2 source successor following factor

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceSuccessorFollowingFactor`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceSuccessorFollowingFactor_pivotRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceSuccessorFollowingFactor_of_ne`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceSuccessorFollowingFactor_oldRow`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2SourceFollowingFactor_successorFollowingFactor_succ`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceSuccessorFollowingFactor_eq_original_of_width_next_eq`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalOriginalRows_successorFollowingFactor`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_eq_originalRows_successorFollowingFactor`

## Statement

Define a source-coordinate successor following factor by replacing only source
row `J+1` of `C` with the transported top row of `Q^-1 C`.  Prove its basic
restrictions: pivot row, off-pivot rows, old top rows, next same-stage
post-pivot tail, actual-width collapse to the original `C`, and terminal
transported-row presentation.

## Proved

The source-order successor following factor is formula-level data whose
restriction to post-pivot columns agrees with the original next same-stage
source following factor.  Its terminal original-row matrix is the existing
transported terminal-row matrix, and the existing stopped terminal `C'`
candidate can be read as terminal original rows of this successor factor.

## Assumed

- Aoyagi displayed Case 2 hypotheses `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.
- Source-coordinate residual data and following factor `C`.
- Actual-width equality only for the collapse theorem.

## Cited

- None in Lean.  This is finite row restriction and equality bookkeeping.

## Deferred

- Chart production of the successor factor.
- Recurrence/exponent post-data from coordinates.
- Old top multiplier or suffix production.
- Full successor product, chart coverage, successor chart-family data,
  transition invariance, Jacobian arithmetic, normal crossings, pole order,
  and RLCT extraction.

## Review

- xhigh source scout `Halley` recommended this source-order object as the
  next broader A4 target after the paper-`C'` audit.
- xhigh reviewer `Locke` passed the slice and recommended the clearer
  `eq_original_of_width_next_eq` theorem name for the actual-width collapse.

## Verification

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `cd lean && lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- `cd lean && scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
