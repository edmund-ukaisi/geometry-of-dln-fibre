# Statement Card - A2 selected-entry signed-box monomial-unit data

Date: 2026-06-25.

## Claim

The selected-entry pivot chart supplies explicit signed-box monomial-unit data
for the finite center square-sum and the absolute formal pivot-first
determinant.

## Lean Names

```text
SelectedEntrySignedBox.Coord
SelectedEntrySignedBox.sourceResidual
SelectedEntrySignedBox.residual
SelectedEntrySignedBox.residualUnit
SelectedEntrySignedBox.sourceDensity
SelectedEntrySignedBox.sourceDensity_eq_abs_pivotFirstJacobian_det
SelectedEntrySignedBox.lossExp
SelectedEntrySignedBox.densityExp
SelectedEntrySignedBox.residual_eq_unit_mul_abs_monomial
SelectedEntrySignedBox.sourceDensity_eq_unit_mul_abs_monomial
SelectedEntrySignedBox.one_le_residualUnit
SelectedEntrySignedBox.densityUnit_nonneg
SelectedEntrySignedBox.densityUnit_le_one
SelectedEntrySignedBox.monomialUnitHypotheses
SelectedEntrySignedBox.monomialLower_sourceDensityBounds
SelectedEntrySignedBox.CenterCoord.residual_eq_unit_mul_abs_monomial
SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_unit_mul_abs_monomial
SelectedEntrySignedBox.CenterCoord.monomialUnitHypotheses
SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds
```

## Inputs Kept Explicit

- finite center `center`;
- selected pivot `pivot : center`;
- arbitrary signed-box radii for the a.e. package.

## Nonclaims

No analytic chart construction, source coverage, transition regularity,
source production, source-measure pushforward, analytic Jacobian theorem,
transported source-density identity, full DLN loss comparison, normal-crossing
extraction, pole order, or RLCT statement is proved.

## Verification

Focused and full builds passed with the worktree-local Lake cache:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` was clean.
