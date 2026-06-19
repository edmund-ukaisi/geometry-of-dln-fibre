# Statement card - A4 Case 2 recurrence-weight update

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`TBD-after-commit`.

Names:

- `DLNFibre.DLN.Aoyagi.introducedLabelFinset_succ_eq_insert`
- `DLNFibre.DLN.Aoyagi.not_mem_introducedLabelFinset_case2_new_before`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ_level_new`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ_var_new`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ_level_of_ne`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ_var_of_ne`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ_case2Gap`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2IntroducedLabelLeastValueGap_succ`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ_levelInvariants`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case2Succ_case2Gap_of_leastValueGap`
- `DLNFibre.DLN.Aoyagi.monomialRec_eq_of_step_eq_on_lt`
- `DLNFibre.DLN.Aoyagi.monomialRec_eq_mul_of_step_eq_mul_at`
- `DLNFibre.DLN.Aoyagi.levelProductStep_insert_eq_mul_of_new`
- `DLNFibre.DLN.Aoyagi.levelProductStep_insert_eq_of_ne`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.step_succ_current_eq_new_mul`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.step_succ_current_eq_of_ne`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.weight_succ_current_eq_of_le`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.weight_succ_current_eq_new_mul_of_ge`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap`

## Statement

Lean now proves the conditional recurrence-weight update behind Aoyagi's
displayed Case 2 formula `b'_i = u*b_i`. If a supplied post-state at
`(S,J+1)` keeps old introduced-label levels and variables unchanged, assigns
the new label `(S,J+1)` level `J`, and assigns it variable `u`, then all
post-state weights from `J+1` onward equal `u` times the old weights.

The checkpoint also proves that the old Case 2 gap is preserved by the concrete
`case2Succ` post-data and that old displayed residual-row flatness remains flat
after the common multiplication by `u`.

## Source Role

Aoyagi's Case 2 displayed chart introduces `u_(S,J+1)` and prints
`b'_(J+1),...,b'_(M(S)) = u_(S,J+1) b_(J+1),...,u_(S,J+1)b_(M(S))`. This
checkpoint isolates the elementary recurrence reason for that update.

## Proved

- Advancing from `(S,J)` to `(S,J+1)` adds exactly the new introduced label
  `(S,J+1)` to the finite introduced-label domain when that label is
  source-valid.
- A single new recurrence factor at level `J` multiplies all recurrence weights
  from `J+1` onward by the selected variable.
- Old weights up to level `J` are unchanged.
- Under the old Case 2 gap, the supplied successor weights are flat on the old
  displayed residual-row range.

## Assumed

- The supplied post-state is the intended post-chart recurrence state.
- Old introduced-label levels and variables are unchanged.
- The new label `(S,J+1)` is source-valid and has level `J`.
- The new label variable is the selected chart variable `u`.
- The old Case 2 gap is assumed where residual flatness is used.

## Not Proved

- No proof that Aoyagi's blow-up chart produces the supplied post-state.
- No repair of the printed Case 2 vector mismatch.
- No proof of source comparability.
- No double-counting of the standalone outside `u` from the PDF display.
- No arbitrary-pivot chart coverage, coordinate regularity/Jacobian, exponent
  update, transition invariant, termination proof, normal-crossing certificate,
  or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-recurrence-weight-update-a4.md`.
- Reproduction check:
  `review-case2-recurrence-weight-update-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
