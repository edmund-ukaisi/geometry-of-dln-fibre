# Statement card - A4 Case 2 source-selected pair wrapper

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`c689e853ab2ddaba4cfae3b8dbe08ec8f1b75b54`.

Names:

- `DLNFibre.DLN.Aoyagi.case2SourceResidualBlock`
- `DLNFibre.DLN.Aoyagi.case2SourceFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedNormalizedMatrixOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedSubstitutionMatrixOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedFollowingFactorOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedTransportedFollowingFactorOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedNormalizedMatrixOfMem_pivot`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedSubstitutionMatrixOfMem_pivot`
- `DLNFibre.DLN.Aoyagi.exists_case2SourceSelectedQP_mul_sourceSubstitution_of_recurrenceStateGap`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.case2SourceSelected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`
- `DLNFibre.DLN.Aoyagi.CorrectedCase2NewLabelCertificate.exists_case2SourceSelectedQP_of_recurrenceStateGap_succWeights_of_postData`

## Statement

Lean now has a source-coordinate wrapper for supplied arbitrary Case 2
residual-block pivot pairs. Given
`p : Nat × Nat` and `hp : p ∈ case2ResidualBlockPivotEntries n S J`, the
membership proof extracts the residual row and column subtype pivots. Source
residual data `Nat × Nat -> R` and source-column following factors are
restricted to the residual row and column subtypes, then fed into the existing
arbitrary selected-pivot recurrence/post-data theorems.

## Source Role

This is a source-coordinate adapter for the finite selected-entry algebra. It
does not add new blow-up geometry. It records that source pair membership in
the Case 2 residual-block center is enough to instantiate the arbitrary
selected-pivot wrappers already proved in subtype coordinates.

## Proved

- Source-coordinate residual data restrict to the Case 2 residual row/column
  subtypes.
- Source-coordinate following factors restrict to the residual columns.
- A source pivot pair in `case2ResidualBlockPivotEntries` instantiates the
  arbitrary selected-pivot recurrence-gap `Q/P` theorem.
- The same source-pair wrapper is available with supplied successor recurrence
  post-data and successor weights.

## Assumed

- A source pivot pair and membership in the residual-block center are supplied.
- The old recurrence state and old Case 2 gap are supplied.
- For successor-weight wrappers, corrected new-label data and supplied
  recurrence post-data are supplied.
- Source residual and following-factor coordinate functions are supplied.

## Not Proved

- No proof that Aoyagi displays non-top-left Case 2 pivot charts.
- No affine blow-up atlas or arbitrary-pivot chart coverage.
- No source-order transition formula for non-displayed pivots.
- No proof that a chart produces the supplied successor state.
- No chart regularity or Jacobian theorem.
- No exponent update or transition invariant.
- No source comparability, normal crossings, or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-source-selected-pair-wrapper-a4.md`.
- Reproduction check:
  `review-case2-source-selected-pair-wrapper-a4.md`.

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
