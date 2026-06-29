# Review: A2 selected-entry chart-target nonzero measure

## Source-scope scout

Reviewer: `Einstein the 4th`, xhigh read-only source-scope review.

Status: PASS.

Findings:

- Recommended the nonzero selected-entry chart-target/source restriction as
  the next faithful checkpoint after the chart-point bridge.
- Confirmed the calculation is elementary selected-entry geometry:
  `x_p = u`, `x_i = u r_i`, with injectivity only off the pivot hyperplane.
- Warned that a one-chart `SelectedEntryAnalyticJacobianVolumeData`
  constructor should wait until the nonzero target field is available, and
  should not fake a natural chart-point product measure.
- Warned not to pursue external/source-prior domination without a concrete
  Aoyagi-only original-prior comparison theorem.

## Lean/API scout

Reviewer: `Beauvoir the 4th`, xhigh read-only Lean/API review.

Status: PASS.

Findings:

- Recommended proving
  `volume_chartMap_image_signedBoxSet_ne_zero` and
  `volume_restrict_chartMap_image_signedBoxSet_ne_zero` directly from image
  geometry, with only `forall i, 0 < R i`.
- Identified the concrete inner box
  `R_p/2 < x_p < R_p`,
  `|x_i| < R_p R_i / 4` for `i != p`.
- Noted that `1 < R i` is unnecessary for a fixed-pivot nonzero theorem; it is
  only needed for existing all-pivot cover statements.
- Recommended using `Measure.restrict_eq_zero` for nonzero restricted
  measures and the existing pushforward equality for weighted source nonzero
  corollaries.

## Implementation review

Reviewer: `Kuhn the 4th`, xhigh read-only implementation review.

Status: PASS.

Findings:

- The inner-box definition and subset proof are faithful to the selected-entry
  substitution `x_p = u`, `x_i = u r_i`.
- Positive radii are enough for the fixed-pivot theorem: they give
  `x_p > 0`, `|x_p| < R_p`, and `|x_i / x_p| < R_i`.
- The nonzero target and restricted-target statements match proved content.
- The full and punctured weighted source-measure nonzero corollaries use only
  the existing selected-entry pushforward equalities.
- The chart-point adapter and two-stage nonzero corollaries are direct
  consequences only; no natural chart-point product measure is asserted.
- No theorem name, docstring, or expedition note overclaims analytic atlas
  construction, source-prior transport, Haar transport, coverage,
  normal-crossing extraction, pole order, or RLCT.

## Verification

Focused builds passed via `scripts/lb`:

```text
DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure
DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge
```

Only pre-existing replay warnings in
`DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity` appeared.

Kuhn also ran direct Lean elaboration for the two touched modules and
`git diff --check 2224caa4`; all passed.
