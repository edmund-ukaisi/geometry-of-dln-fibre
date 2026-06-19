# Statement card - A4 Case 1 selected-old Unit chart-family boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedIntroduced`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedLevel`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_mem_center`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.chart_regular_selectedOld`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.transition_regular_selectedOld_of_mem`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.transition_regular_of_mem_selectedOld`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_selectedEntryChartMap_value_mem`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_center_dvd`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_centerIdeal_eq_span_singleton`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.sourceMatrix_identity_postWeights`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.sourceCoordinates_identity_postWeights`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldUnitSuppliedChartFamilyBoundary.updateExponentCertificates`

## Statement

Lean now packages a supplied chart-family/principalization boundary for
Aoyagi Case 1(1)'s selected-old `Unit` chart. It combines the already supplied
selected-old lowered recurrence boundary with the supplied finite Case 1
chart-family boundary.

The package projects selected-label facts, selected-old finite center
membership, supplied regularity for the selected-old chart token, supplied
transition regularity from/to any finite Case 1 center generator, finite
selected-entry principalization for the `Unit` token, the pre/post recurrence
source identities, and the same-domain exponent update.

## Source Role

This is the chart-family wrapper for the Case 1(1) branch where the selected
chart denominator is the old exceptional variable `u_(s0,k0)` itself. In the
Lean finite center this selected-old generator is represented by
`Sum.inl () : Case1CenterGenerator`. The token is bookkeeping only; the old
source label `(s0,k0)` and first-jump level `J+J1` still come from the carried
selected-old boundary.

## Proved

- The selected old source label is introduced and has level `J+J1`, through
  the lowered recurrence boundary.
- The selected-old `Unit` token is a finite Case 1 center generator.
- Supplied chart regularity applies to the selected-old token.
- Supplied transition regularity applies from/to the selected-old token and
  any finite Case 1 center generator.
- In the selected-old finite selected-entry chart, the selected scalar occurs
  among the transformed center values, divides every transformed center
  generator, and generates the transformed finite center ideal.
- The supplied pre/post recurrence source identities and same-domain exponent
  certificate update remain available.

## Assumed

- Supplied selected-old lowered recurrence data:

```text
pre.step  = mulStepAt(baseStep,u,J+J1),
post.step = mulStepAt(baseStep,u,J).
```

- Supplied same-domain selected-old exponent boundary.
- Supplied Case 1 finite chart-family regularity and transition regularity.

## Not Proved

- No construction of the selected-old chart or affine atlas.
- No derivation of the `Unit` token's hidden source label `(s0,k0)`.
- No derivation of `baseStep`, `pre`, or `post` from source coordinates.
- No proof that coordinates produce recurrence post-data.
- No domain advancement to `(S,J+1)` and no displayed Case 1(2) pivot.
- No `Q/P`, chart coverage, regularity proof from coordinates, transition
  formula, Jacobian accounting, normal crossings, RLCT extraction, or full
  transition invariant.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-unit-chart-family-boundary-a4.md`.
- Review artifact:
  `review-case1-selected-old-unit-chart-family-boundary-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
