# Statement card - A4 Case 2 transported following factor with monomial rows

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`caaa41c5af3d5c78d681000d1ce3a9a30b89bba8`.

Names:

- `DLNFibre.DLN.Aoyagi.case2ResidualRowLevel`
- `DLNFibre.DLN.Aoyagi.case2ResidualRowLevel_ge`
- `DLNFibre.DLN.Aoyagi.case2ResidualRowLevel_displayedPivotRow`
- `DLNFibre.DLN.Aoyagi.case2DisplayedTransportedFollowingFactor`
- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec`

## Statement

Lean now names the displayed Case 2 following-factor update
`Q^{-1} C_pivot_first` and proves a pivot-first `Q/P` product identity when
the updated residual row weights are `u * monomialRec step rowLevel`.

## Source role

Aoyagi's displayed Case 2 calculation updates the following factor by
`C'_J^(S+1)=Q^{-1}C_J^(S+1)` and uses quotients
`b'_i / b'_(J+1)` in the `P` matrix. This checkpoint proves the finite
matrix identity when those quotients are supplied by the monomial recurrence
and the fact that every residual source row has label at least `J+1`.

## Proved

- The residual source row label is named and bounded below by `J+1`.
- The displayed transported following factor is named as
  `Q^{-1} * case2DisplayedFollowingFactor`.
- If residual row weights are `u * monomialRec step rowLevel`, quotient
  witnesses for the `P` operation exist by recurrence divisibility.
- The displayed pivot-first `Q/P` product identity holds with the transported
  following factor on the right-hand side.

## Assumed

- The residual block is already in displayed Case 2 coordinates.
- The selected pivot is the displayed top-left residual entry.
- Row weights are already represented by the row-index monomial recurrence
  used in the theorem.

## Not proved

- No proof that Aoyagi's recursive state produces these row-index weights.
- No proof of the Case 2 flat row-weight hypothesis or source `b` recurrence.
- No full source blockdiag identity including the top `J` rows.
- No arbitrary selected-entry pivot chart or chart coverage.
- No polynomial automorphism/Jacobian theorem for the full chart.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-case2-transported-following-factor-monomial-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
