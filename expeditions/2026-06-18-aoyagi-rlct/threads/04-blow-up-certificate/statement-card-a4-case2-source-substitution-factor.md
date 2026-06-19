# Statement card - A4 Case 2 source-substitution factor

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`e258664c1c9e2c44a412b30ac8abb743c886236b`.

Names:

- `DLNFibre.DLN.Aoyagi.diagonal_mul_selectedEntrySubstitutionMatrix`
- `DLNFibre.DLN.Aoyagi.pivotFirst_diagonal_mul_selectedEntrySubstitutionMatrix`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSubstitutionMatrix`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSubstitutionMatrix_eq_mul_normalized`
- `DLNFibre.DLN.Aoyagi.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst`
- `DLNFibre.DLN.Aoyagi.case2Displayed_diagonal_mul_substitutionMatrix_mul_followingFactor`
- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights`

## Statement

Lean now proves the finite source-substitution factorisation used in Aoyagi's
displayed Case 2 chart: multiplying the source-substituted residual block by
old row weights is the same as multiplying the normalised residual block by
row weights updated to `u * oldWeight`.

## Source role

Aoyagi's displayed chart writes `D_J = u_(S,J+1) D'_J` and then performs the
`Q/P` operations on the normalised block `D'_J`. This checkpoint proves the
finite equality that moves the selected factor `u_(S,J+1)` from the residual
block entries into the displayed row weights before applying the existing
pivot-first `Q/P` theorem.

## Proved

- The selected-entry substitution matrix is `u` times the normalised matrix.
- `diag(weight) * sourceSubstitutedBlock` equals
  `diag(i => u * weight i) * normalisedBlock`.
- After pivot-first reindexing, the updated diagonal is exactly the split
  `weightedPivotDiagonal`.
- With a residual following factor included, the product reindexes to the
  pivot-first product expected by the displayed Case 2 `Q/P` theorem.
- Under flat displayed row weights, the displayed Case 2 `Q/P` theorem applies
  directly to the source-substituted block after this factoring.

## Assumed

- The residual block has already been restricted to the displayed Case 2
  residual coordinates.
- The selected pivot is the displayed top-left residual entry.
- Row weights are supplied in displayed residual-row coordinates; flatness is
  assumed for the final `Q/P` wrapper.
- The selected variable is counted once via `newWeight_i = u * oldWeight_i`.

## Not proved

- No full source blockdiag identity including the top `J` rows.
- No arbitrary selected-entry pivot chart or chart coverage.
- No polynomial automorphism/Jacobian theorem for the full chart.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-case2-source-substitution-factor-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
