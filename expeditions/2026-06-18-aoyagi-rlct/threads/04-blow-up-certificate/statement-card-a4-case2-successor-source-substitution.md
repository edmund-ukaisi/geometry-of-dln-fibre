# Statement card - A4 Case 2 successor source substitution

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ pending checkpoint
commit.

Names:

- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`

## Statement

Lean now connects the displayed Case 2 source-substitution algebra to supplied
successor recurrence weights. The left side remains the source-substituted
residual block weighted by the old state:

```text
diag(pre residual weights) * D_J.
```

Using `D_J = u D'_J` and the supplied recurrence update
`post.weight_i = u * pre.weight_i` for `i >= J+1`, the pivot-first normalised
right side can be written with `post.weight` rather than with ad hoc
`u * pre.weight` factors.

## Source Role

Aoyagi's Case 2 display combines the selected-entry substitution
`D_J = u_(S,J+1) D'_J` with the row-weight update `b'_i = u_(S,J+1)b_i`. This
checkpoint proves the finite algebraic handoff between those two displayed
lines, using the recurrence-weight update formalised in the previous
checkpoint.

## Proved

- The pivot-first source-substituted block with old row weights equals the
  normalised block with supplied successor row weights.
- The displayed source-substitution `Q/P` identity under the old Case 2 gap
  has a cleared-side diagonal written as `post.weight (J+1)` and
  `post.weight rowLevel` on the old displayed residual rows.
- The selected variable is counted once, via the successor weights.

## Assumed

- A `CorrectedCase2NewLabelCertificate L n S J`, whose new introduced label is
  `(S,J+1)`.
- A supplied successor recurrence state at `(S,J+1)`.
- Old introduced-label levels and variables are unchanged in the supplied
  successor state.
- The new label has level `J` and variable `u`.
- The old Case 2 gap is assumed for the `Q/P` wrapper.

## Not Proved

- No proof that a blow-up chart produces the supplied successor recurrence
  state.
- No arbitrary-pivot chart transport or chart coverage.
- No coordinate regularity/Jacobian theorem.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.
- No repair of the printed Case 2 vector mismatch or source comparability
  sentence.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-successor-source-substitution-a4.md`.
- Reproduction check:
  `review-case2-successor-source-substitution-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
