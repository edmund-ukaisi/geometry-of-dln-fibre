# Statement card - A4 Case 1 selected-old recurrence post weight

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.monomialRec_mulStepAt_case1_selectedOld_postWeight`
- `DLNFibre.DLN.Aoyagi.case1SelectedOldPostWeight_eq_monomialRec_loweredLevel`
- `DLNFibre.DLN.Aoyagi.case1SelectedOld_diagonal_mul_sourceMatrix_loweredLevel`
- `DLNFibre.DLN.Aoyagi.case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates_loweredLevel`

## Statement

Lean proves the elementary recurrence-weight calculation behind Aoyagi
Case 1(1).  Starting from a supplied base recurrence, moving the selected old
factor from level `J+J1` down to level `J` gives the piecewise post-weight
convention on active residual rows:

```text
b'_i =
  u * b_i, if i <= J+J1,
  b_i,     otherwise.
```

The matrix corollaries rewrite the Case 1(1) source-coordinate row-strip
identity with the right diagonal expressed as the lowered-level recurrence.

## Source Role

This matches Aoyagi PDF p. 16, where Case 1(1) lowers the already selected old
label and prints the strip weight updates
`b'_(J+1),...,b'_(J+J1)`.

## Proved

- Pure `mulStepAt` recurrence identity for active rows.
- Residual-row specialization using `case1ResidualRowStrip`.
- Generic and source-coordinate source-matrix identities with the lowered
  recurrence on the right diagonal.

## Not Proved

- No construction of the selected-old chart.
- No construction of the supplied base recurrence from source recurrence data.
- No recurrence-state post-data theorem for moving `(s0,k0)` from level
  `J+J1` to `J`.
- No introduction of `(S,J+1)` and no use of the displayed Case 1(2) pivot.
- No `Q/P`, chart coverage, regularity, transition regularity, Jacobian,
  normal crossings, RLCT extraction, or full transition invariant.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-recurrence-postweight-a4.md`.
- Review artifact:
  `review-case1-selected-old-recurrence-postweight-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
