# Statement card - A4 Case 2 exponent update data

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ pending checkpoint
commit.

Name:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_updateData_of_prefixBound`

## Statement

Lean now has a concrete update-data wrapper for corrected Case 2 exponent
domain extension. Given an old `IntroducedLabelExponentCertificates` package at
`(S,J)` and the continuation bound `J+1 <= mu_(S+1)`, the theorem extends the
package to `(S,J+1)` using total assignment overrides:

- the new label vector is `correctedCase2PivotVector n S J`;
- the new numerator is `(mu_S-J)(n_(S+1)-J)`;
- the new least value is `J`;
- all old introduced-label assignments are unchanged.

## Source Role

This names the corrected Case 2 new-label exponent update as concrete
post-data. It is a wrapper around the existing corrected new-label certificate
and domain-extension theorem.

## Proved

- `(S,J+1)` is not an old introduced label, so selected-label update functions
  leave all old introduced labels unchanged.
- At `(S,J+1)`, the same update functions reduce to the corrected vector,
  numerator, and least value.
- Under the continuation bound, the existing corrected Case 2 new-label
  certificate supplies the new one-label certificate, so the exponent
  certificate package extends to `(S,J+1)`.

## Assumed

- The old introduced-label exponent certificate package is supplied.
- The continuation bound `J+1 <= mu_(S+1)` is supplied.
- The corrected prefix-minimum Case 2 vector is used for the new label.

## Not Proved

- No chart production.
- No proof that a chart leaves old exponent assignments unchanged.
- No recurrence-post-data implication for exponent data.
- No full exponent transition invariant.
- No arbitrary-pivot transport.
- No source comparability.
- No normal-crossing certificate or RLCT extraction.
- No claim that the corrected vector is the PDF's printed Case 2 vector.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-exponent-update-data-a4.md`.
- Reproduction check:
  `review-case2-exponent-update-data-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
