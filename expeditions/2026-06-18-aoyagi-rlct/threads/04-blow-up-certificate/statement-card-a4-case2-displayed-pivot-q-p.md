# Statement card - A4 Case 2 displayed pivot `Q/P`

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `<pending Lean commit>`.

Names:

- `DLNFibre.DLN.Aoyagi.Case2ResidualRowIndex`
- `DLNFibre.DLN.Aoyagi.Case2ResidualColIndex`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotRow`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPivotCol`
- `DLNFibre.DLN.Aoyagi.selectedEntryNormalizedMap`
- `DLNFibre.DLN.Aoyagi.selectedEntryNormalizedMap_pivot`
- `DLNFibre.DLN.Aoyagi.selectedEntryNormalizedMap_of_ne`
- `DLNFibre.DLN.Aoyagi.selectedEntryChartMap_eq_mul_normalized`
- `DLNFibre.DLN.Aoyagi.selectedEntryNormalizedMatrix`
- `DLNFibre.DLN.Aoyagi.selectedEntrySubstitutionMatrix`
- `DLNFibre.DLN.Aoyagi.selectedEntryNormalizedMatrix_pivot`
- `DLNFibre.DLN.Aoyagi.selectedEntrySubstitutionMatrix_pivot`
- `DLNFibre.DLN.Aoyagi.selectedEntryNormalizedMatrix_of_ne`
- `DLNFibre.DLN.Aoyagi.selectedEntrySubstitutionMatrix_eq_mul_normalized`
- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_mul_of_flat_weights`

## Statement

Lean now instantiates the already-proved pivot-first `Q/P` algebra for the
source-displayed Case 2 top-left selected-entry substitution. Under
`J+1 <= mu_(S+1)`, the displayed row and column `J+1` are packaged as finite
residual-block indices. The selected-entry substitution is split into a
selected variable times a normalised matrix whose displayed pivot entry is `1`.

The theorem `exists_case2DisplayedQP_mul_of_flat_weights` assumes flat
residual-row weights in these displayed coordinates and proves the
product-preservation `Q/P` identity with the following factor multiplied by
`pivotQinv`.

## Source role

Aoyagi displays the Case 2 chart selecting `d_(J+1,J+1)`. This checkpoint
formalises that displayed local algebra after separating the selected-entry
normalisation from the row-weight quotient witnesses. It keeps the corrected
prefix-minimum exponent vector separate from the printed-vector mismatch.

## Proved

- `J+1` is a finite residual row and column index under the source
  continuation bound.
- A selected-entry substitution factors as `u` times a normalised substitution.
- The normalised displayed matrix has pivot entry `1`.
- Flat displayed residual-row weights supply the quotient witnesses needed by
  the pivot-first `Q/P` product identity.

## Assumed

- The following factor is already expressed in the displayed pivot-first column
  coordinates.
- Row weights are already expressed in the displayed residual-row coordinates.
- The theorem is local to the displayed chart and does not assert coverage.

## Not proved

- No arbitrary selected-entry Case 2 pivot chart.
- No affine blow-up atlas, row/column permutation reduction, or chart coverage.
- No full coordinate/weight transport theorem from source variables.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-case2-displayed-pivot-q-p-a4.md`.
- Xhigh source and hardener reports recommended keeping this checkpoint to the
  source-displayed top-left pivot before attempting arbitrary chart coverage.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
