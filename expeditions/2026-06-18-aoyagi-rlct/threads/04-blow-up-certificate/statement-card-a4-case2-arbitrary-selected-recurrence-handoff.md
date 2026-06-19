# Statement card - A4 Case 2 arbitrary selected-entry recurrence handoff

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`pending-checkpoint`.

Names:

- `DLNFibre.DLN.Aoyagi.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData`

## Statement

Lean now lifts the arbitrary selected-entry Case 2 source-substitution algebra
to the packaged recurrence-state boundary.

For any supplied Case 2 residual-row pivot and residual-column pivot:

- an old `IntroducedLabelRecurrenceState` satisfying `case2Gap` supplies the
  flat residual-row weights needed by the arbitrary selected-pivot `Q/P`
  theorem;
- a supplied successor recurrence state satisfying the Case 2 post-data
  hypotheses rewrites the right-side diagonal from `u * pre.weight` to
  `post.weight`;
- `_of_postData` wrappers accept the named
  `IntroducedLabelRecurrenceState.Case2SuppliedPostData` package.

## Source Role

This is the arbitrary selected-pivot analogue of the displayed Case 2
successor-weight handoff. It keeps recurrence production and chart coverage out
of the theorem statement.

## Proved

- Old recurrence-state Case 2 gap gives flat old residual-row weights relative
  to any supplied selected pivot row.
- The arbitrary selected-pivot source-substitution `Q/P` theorem applies to
  those weights.
- Supplied successor recurrence post-data rewrites every old residual row
  weight multiplied by `u` as the corresponding `post.weight`.
- The same handoff is available through the named post-data package.

## Assumed

- A residual-row pivot and residual-column pivot are supplied.
- The old recurrence state and old Case 2 gap are supplied.
- For successor-weight rewriting, the corrected new-label certificate and
  supplied recurrence post-state data are supplied.

## Not Proved

- No proof that a blow-up chart produces the supplied successor state.
- No arbitrary-pivot chart coverage.
- No affine blow-up atlas, chart regularity, or Jacobian theorem.
- No exponent update or transition invariant.
- No source comparability, normal crossings, or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-arbitrary-selected-recurrence-handoff-a4.md`.
- Reproduction check:
  `review-case2-arbitrary-selected-recurrence-handoff-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From repository root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory: no Lean forbidden-token hits; matches are historical prose records
  of clean scans.
