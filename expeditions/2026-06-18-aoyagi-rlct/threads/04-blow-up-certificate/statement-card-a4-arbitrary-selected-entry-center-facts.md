# Statement card - A4 arbitrary selected-entry center facts

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `36e8725`.

Names:

- `DLNFibre.DLN.Aoyagi.case2_selectedEntryChartMap_value_mem_of_mem`
- `DLNFibre.DLN.Aoyagi.case2_selectedEntryChartMap_center_dvd_of_mem`
- `DLNFibre.DLN.Aoyagi.case1_selectedEntryChartMap_value_mem_of_mem`
- `DLNFibre.DLN.Aoyagi.case1_selectedEntryChartMap_center_dvd_of_mem`

## Statement

Lean specializes the finite map `selectedEntryChartMap` to pivots already
proved to lie in the relevant finite center: `case2ResidualBlockPivotEntries n
S J` in Case 2 and `case1CenterGenerators n S J J1` in Case 1. For such a
pivot, the Case-specific theorems prove two finite facts: `u` occurs in the
value set of the substitution map, witnessed by the pivot, and `u` divides
`selectedEntryChartMap pivot u residual g` for every generator `g` in the same
finite center.

## Source role

Aoyagi displays the selected old-variable branch in Case 1(1) and the top-left
`d_(J+1,J+1)` pivot substitutions in Case 1(2) and Case 2. The paper does not
spell out the non-displayed selected-generator charts or their `Q/P` formulas.
These lemmas are a formalization scaffold inferred from the finite coordinate
centers, not reproduced source formulas.

For Case 1, the `Unit` branch is still an externally chosen old exceptional
variable, and row-strip membership is only membership in
`case1CenterGenerators`; this theorem does not add old-label validity,
level/minimality/comparability, the `J+J1 <= mu_S` residual-block containment,
or first-jump hypotheses.

## Proved

- Any selected Case 2 residual-block entry has value `u` in the finite
  selected-entry value set.
- Every transformed Case 2 residual-block center entry is divisible by `u`.
- Any selected Case 1 center generator has value `u` in the finite
  selected-entry value set.
- Every transformed Case 1 center generator is divisible by `u`.

## Not proved

- No affine blow-up atlas or chart coverage theorem.
- No non-displayed transition theorem.
- No polynomial coordinate regularity, localization/unit fact, Jacobian
  behavior, row/column permutation symmetry, `Q/P` matrix transition formula,
  exponent update, termination proof, normal-crossing certificate, or RLCT
  extraction.

## Status

- Sorry-free at `36e8725`; xhigh source-scope review completed and caveat
  tightening incorporated.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
