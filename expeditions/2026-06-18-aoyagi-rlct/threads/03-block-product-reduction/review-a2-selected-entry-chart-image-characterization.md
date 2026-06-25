# Review - A2 selected-entry chart-image characterization

Date: 2026-06-25.

Reviewer: Halley, xhigh source/API review.

Verdict: PASS.  No blocking findings.

## Scope

Reviewed the finite selected-entry chart-image theorem:

```text
SelectedEntrySignedBox.CenterCoord.mem_chartMap_image_signedBoxSet_iff
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-selected-entry-chart-image-characterization.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-selected-entry-chart-image-characterization.md
```

## Checks

- The origin branch is correct: if the selected pivot coordinate is zero,
  `chartMap pivot y = 0`.
- The positivity assumption `forall i, 0 < R i` is exactly what makes the
  reverse origin branch valid by choosing `y = 0`.
- The nonzero-pivot horn is exact: the inverse on this branch is
  `y pivot = x pivot` and `y i = x i / x pivot` for `i != pivot`.
- The theorem placement in `SelectedEntrySignedBoxMeasure.lean` is appropriate:
  it is finite selected-entry chart algebra and introduces no original-loss,
  Core, or closed-form dependency.
- The reproduction, statement card, and ledgers keep source-stratum coverage,
  source-measure identification, fixed-base residual readout, normal crossings,
  pole order, and RLCT outside the claim.

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure
```

Nonblocking wording nits were fixed after review: the reproduction status no
longer says "before Lean", and the `sourceResidual` docstring now clarifies
that the chart's pivot branch ignores the residual value at the pivot.
