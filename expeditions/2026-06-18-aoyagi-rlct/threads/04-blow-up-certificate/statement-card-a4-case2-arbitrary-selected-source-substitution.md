# Statement card - A4 Case 2 arbitrary selected-entry source substitution

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`19046e50fa4b57e9286e0b15c7d9547b9dd6e56c`.

Names:

- `DLNFibre.DLN.Aoyagi.case2ResidualBlockPivotRowOfMem`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockPivotColOfMem`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockPivotOfMem_pair`
- `DLNFibre.DLN.Aoyagi.case2SelectedNormalizedMatrix`
- `DLNFibre.DLN.Aoyagi.case2SelectedSubstitutionMatrix`
- `DLNFibre.DLN.Aoyagi.case2SelectedSubstitutionMatrix_eq_mul_normalized`
- `DLNFibre.DLN.Aoyagi.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst`
- `DLNFibre.DLN.Aoyagi.case2SelectedFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2SelectedTransportedFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2SelectedNormalizedMatrix_mul_followingFactor`
- `DLNFibre.DLN.Aoyagi.case2Selected_diagonal_mul_substitutionMatrix_mul_followingFactor`
- `DLNFibre.DLN.Aoyagi.exists_case2SelectedQP_mul_sourceSubstitution_of_forall_dvd`
- `DLNFibre.DLN.Aoyagi.exists_case2SelectedQP_mul_sourceSubstitution_of_flat_weights`

## Statement

Lean now has arbitrary selected-entry finite algebra for the Case 2 residual
block. A pivot is supplied as a residual-row subtype and residual-column subtype
or extracted from membership in `case2ResidualBlockPivotEntries`.

For any selected pivot, selected variable `u`, row weights, residual
coordinates, and following factor:

- the source-substituted residual block is `u` times the normalised selected
  matrix;
- after pivot-first row/column reindexing, the selected variable is absorbed
  into the row diagonal as `u * weight`;
- the following factor is reindexed into pivot-first column order;
- the existing pivot-first `Q/P` identity applies under explicit divisibility
  of every pivot-complement row weight by the selected pivot-row weight, after
  pivot-first reindexing, with flat row weights as a corollary.

## Source Role

This is the arbitrary selected-entry analogue of the displayed top-left Case 2
source-substitution bridge. It is an inferred finite-algebra scaffold for the
chart family, not a source-displayed arbitrary-pivot theorem.

## Proved

- A finite pivot entry in the Case 2 residual-block center determines row and
  column subtype pivots, with a paired source-coordinate equality.
- The selected-entry substitution factors as `u` times the normalised matrix.
- Pivot-first reindexing transports the row diagonal and following factor.
- Conditional arbitrary selected-pivot `Q/P` follows from explicit quotient
  divisibility or flat residual-row weights.

## Assumed

- The selected row and column pivots are supplied.
- Row weights are supplied on the residual-row subtype.
- The following factor is supplied on the residual-column subtype.
- Divisibility or flatness of row weights is supplied for the conditional
  `Q/P` theorem.

## Not Proved

- No affine blow-up atlas or chart coverage.
- No claim that Aoyagi displays arbitrary non-top-left pivot charts.
- No chart regularity or Jacobian theorem.
- No recurrence post-state production.
- No exponent update or transition invariant.
- No source comparability, normal crossings, or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-arbitrary-selected-source-substitution-a4.md`.
- Reproduction check:
  `review-case2-arbitrary-selected-source-substitution-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From worktree root: `git diff --check`: passed.
