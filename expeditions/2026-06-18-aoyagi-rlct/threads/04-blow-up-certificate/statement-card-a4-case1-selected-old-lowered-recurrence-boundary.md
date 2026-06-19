# Statement card - A4 Case 1 selected-old lowered recurrence boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary.selectedIntroduced`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary.selectedLevel`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary.selectedOldPostWeight_eq_postWeight`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary.sourceMatrix_identity_postWeights`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary.sourceCoordinates_identity_postWeights`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary.updateExponentCertificates`

## Statement

Lean now packages a supplied recurrence-state boundary for Aoyagi Case 1(1).
The boundary assumes:

```text
pre.step  = mulStepAt(baseStep,u,J+J1),
post.step = mulStepAt(baseStep,u,J).
```

It combines these supplied recurrence equalities with the previously proved
same-domain selected-old exponent boundary.  The main projection rewrites the
piecewise Case 1(1) selected-old post weights as the supplied `post` recurrence
weights on residual rows, then rewrites the source-coordinate row-strip
identity with `pre.weight` on the left and `post.weight` on the right.

## Source Role

This is the source-facing version of the Case 1(1) recurrence calculation:
the selected old factor is moved from level `J+J1` to level `J`, while the
introduced-label domain remains `(S,J)`.

## Proved

- The boundary projects selected introducedness and selected level from the
  existing first-jump package.
- Piecewise selected-old post weights agree with supplied post recurrence
  weights under the supplied base-step equalities.
- Generic and source-coordinate source-matrix identities can be written using
  supplied pre/post recurrence weights.
- The same-domain exponent certificate update is re-exported from the
  selected-old same-domain boundary.

## Not Proved

- No construction of the selected-old chart.
- No derivation of `baseStep`, `pre`, or `post` from source coordinates.
- No proof that coordinates produce recurrence post-data.
- No domain advancement to `(S,J+1)` and no displayed Case 1(2) pivot.
- No `Q/P`, chart coverage, regularity, transition regularity, Jacobian,
  normal crossings, RLCT extraction, or full transition invariant.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-lowered-recurrence-boundary-a4.md`.
- Review artifact:
  `review-case1-selected-old-lowered-recurrence-boundary-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
