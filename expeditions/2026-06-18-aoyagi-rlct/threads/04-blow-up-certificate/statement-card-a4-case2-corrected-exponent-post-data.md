# Statement card - A4 Case 2 corrected exponent post-data

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`a54fe3e73780fd417b35ad99e88c86f71cad102d`.

Names:

- `DLNFibre.DLN.Aoyagi.Case2CorrectedExponentPostData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_postData`
- `DLNFibre.DLN.Aoyagi.Case2CorrectedExponentPostData.updateSelected`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case2SuppliedPostData.levelInvariants_of_correctedExponentPostData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case2SuppliedPostData.case2Gap_of_leastValueGap_of_correctedExponentPostData`

## Statement

Lean now packages supplied corrected Case 2 exponent post-data for a `J`-advance.
The package records exactly six exponent-map equalities:

- old introduced-label vectors are unchanged;
- old introduced-label numerators are unchanged;
- old introduced-label least values are unchanged;
- the new label vector is `correctedCase2PivotVector n S J`;
- the new label numerator is `(mu_S-J)(n_(S+1)-J)`;
- the new label least value is `J`.

Using this package and a corrected new-label certificate, Lean extends an old
`IntroducedLabelExponentCertificates` package from `(S,J)` to `(S,J+1)`.

The same package also interacts with supplied recurrence post-data: if old
least values equal old recurrence levels and the old integer least-value Case 2
gap holds, then the supplied successor recurrence state satisfies the successor
Nat-valued `case2Gap`.

## Source Role

This is a corrected-certificate package. It intentionally uses the
prefix-minimum repaired Case 2 vector. It is not a source-faithful package of
the PDF's printed vector data.

The source-facing role is to separate recurrence post-data from exponent
post-data while making their shared least-value/level invariant boundary
explicit.

## Proved

- The six supplied corrected exponent post-data fields imply all-label exponent
  certificate extension at `(S,J+1)`.
- The concrete selected-label update functions supply those six fields.
- Supplied recurrence post-data plus supplied corrected exponent post-data
  preserve the `leastValue = level` bridge across the Case 2 `J`-advance.
- The same supplied data converts an old integer least-value gap into the
  successor recurrence-level `case2Gap`.
- The existing concrete update-data theorem now factors through this package.

## Assumed

- The old exponent certificate package is supplied.
- The corrected new-label certificate is supplied for the new label.
- For the recurrence/gap bridge, recurrence post-data, the old
  least-value/level bridge, and the old integer least-value gap are supplied.

## Not Proved

- No chart production or proof that charts preserve old exponent assignments.
- No full exponent transition invariant.
- No arbitrary-pivot transport.
- No source comparability.
- No chart coverage, regularity, Jacobian theorem, normal-crossing certificate,
  or RLCT extraction.
- No claim that the corrected vector is the PDF's printed Case 2 vector.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-corrected-exponent-post-data-a4.md`.
- Reproduction check:
  `review-case2-corrected-exponent-post-data-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From worktree root: `git diff --check`: passed.
