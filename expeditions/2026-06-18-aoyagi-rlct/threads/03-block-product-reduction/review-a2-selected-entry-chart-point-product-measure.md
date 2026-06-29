# Review: A2 selected-entry chart-point product measure

## Source-scope scout

Reviewer: `Newton the 4th`, xhigh read-only source-scope review.

Status: PASS.

Findings:

- Confirmed this is a faithful small A2 hardening checkpoint.
- Identified the intended statement as the finite product-coordinate split
  for `chartPointAdapter`, with no positivity hypothesis on radii.
- Confirmed that the theorem should not be described as analytic atlas,
  source-prior, Haar transport, coverage, normal-crossing extraction, pole
  order, or RLCT progress.
- Noted that the Jacobian factor belongs to `formalChartMap`, not to the
  adapter itself.

## Lean/API scout

Reviewer: `Hume the 4th`, xhigh read-only Lean/API review.

Status: PASS.

Findings:

- Recommended proving the result through a measurable equivalence, not by
  raw rectangle extensionality.
- Identified the relevant Mathlib APIs:
  `measurePreserving_piEquivPiSubtypeProd`,
  `measurePreserving_piUnique`, `measurePreserving_piCongrLeft`,
  `MeasurePreserving.prod`, `MeasurePreserving.comp`, and
  `MeasurePreserving.map_eq`.
- Identified the main bookkeeping issue as reindexing the non-pivot subtype
  to `center.erase pivot.1`.

## Implementation review

Reviewer: `Kant the 4th`, xhigh read-only implementation review.

Status: PASS.

Findings:

- The new Lean diff stays within the finite chart-point/product-measure
  boundary.
- The equivalence and coordinate lemmas prove only that finite center
  coordinates split into the pivot coordinate plus erased non-pivot
  coordinates, and that this split is exactly `chartPointAdapter`.
- The measure statements are correctly limited to the raw finite signed-box
  product measure and its chart-point product split.
- The theorem names describe the finite adapter/product-measure bridge without
  overclaiming.
- No analytic atlas coverage, original source-prior identification, weighted
  source-density transport, normal-crossing extraction, or RLCT extraction is
  asserted.

## Verification

Focused build passed via `lean/scripts/lb`:

```text
DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge
```

Only pre-existing replay warnings in
`DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity` appeared.

Kant also ran direct Lean elaboration for the touched module and
`git diff --check`; both passed.
