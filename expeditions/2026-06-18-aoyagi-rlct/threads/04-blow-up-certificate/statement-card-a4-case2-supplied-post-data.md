# Statement card - A4 Case 2 supplied post-data

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`037edd679b782081988b6693670a6322e25bc2bc`.

Names:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case2SuppliedPostData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ_case2SuppliedPostData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_eq_new_mul_of_ge`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul_of_postData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_residual_flat_of_preGap`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap_of_postData`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData`

## Statement

Lean now packages the repeated supplied post-state assumptions for a Case 2
`J`-advance. The package records only:

- old introduced-label levels are unchanged;
- old introduced-label variables are unchanged;
- the new label `(S,J+1)` has level `J`;
- the new label variable is `u`.

It is recurrence-local. The old Case 2 gap, displayed pivot bounds, and
corrected new-label certificate remain separate hypotheses in the theorems that
actually need them.

## Source Role

For the row-weight recurrence update, Aoyagi's displayed Case 2 calculation
uses exactly this post-data to derive `b'_i = u b_i`. This checkpoint names
that data and provides thin wrappers around the previously proved recurrence
update, residual flatness, and displayed source-substitution `Q/P` handoff.

## Proved

- The concrete `pre.case2Succ u` state satisfies the supplied post-data
  package.
- Under actual source-validity of `(S,J+1)`, the package gives
  `post.weight i = u * pre.weight i` for every `J+1 <= i`.
- Under the old Case 2 gap, the supplied successor weights are flat on the old
  displayed residual rows.
- Corrected-certificate wrappers derive the same consequences using the
  certificate's source-valid new-label field.
- The displayed pivot-first source-substitution and displayed `Q/P` wrappers
  now accept the post-data package instead of four separate old/new data
  hypotheses.

## Assumed

- The post-state is supplied.
- The package fields are assumptions about old-label agreement and new-label
  level/variable assignment.
- Source validity, the old Case 2 gap, and displayed pivot bounds are supplied
  separately where needed.

## Not Proved

- No proof that a blow-up chart produces the supplied post-state.
- No arbitrary-pivot chart coverage.
- No coordinate regularity/Jacobian theorem.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.
- No repair of the printed Case 2 vector mismatch or source comparability
  sentence.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-supplied-post-data-a4.md`.
- Reproduction check:
  `review-case2-supplied-post-data-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
