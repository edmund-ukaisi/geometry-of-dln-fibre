# Statement Card - A2 selected-entry chart Jacobian pushforward

Date: 2026-06-25.

## Claim

For the finite center-indexed selected-entry chart
`y_p |-> y_p`, `y_i |-> y_p * y_i`, the actual Frechet derivative has
determinant `y_p^(|center|-1)`, and the chart pushes forward the signed-box
product measure weighted by `|y_p|^(|center|-1)` to Lebesgue measure
restricted to the signed-box chart image.

## Lean Names

```text
SelectedEntrySignedBox.CenterCoord.chartMapFDeriv_det
SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_abs_chartMapFDeriv_det
SelectedEntrySignedBox.CenterCoord.signedBoxMeasure_eq_volume_restrict
SelectedEntrySignedBox.CenterCoord.volume_pivot_hyperplane_eq_zero
SelectedEntrySignedBox.CenterCoord.signedBoxSet_ae_eq_inter_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet
SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image
SelectedEntrySignedBox.CenterCoord.chartMap_image_signedBoxSet_ae_eq_inter_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
```

## Inputs Kept Explicit

- finite center `center`;
- selected pivot `pivot : center`;
- signed-box radii `R : center -> R`.

The proof uses Mathlib's finite-dimensional change-of-variables theorem
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` only after
restricting to the nonzero-pivot locus, where the chart is injective.

## Nonclaims

No p.13 source chart is constructed.  No source coverage, original-source
measure identity, full DLN loss comparison, normal-crossing certificate, pole
order theorem, or RLCT extraction is proved.

## Verification

Focused build passed with the worktree-local Lake cache:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure
```

Independent xhigh review passed after follow-up fixes for image measurability,
module docstring drift, and dependency hygiene.
