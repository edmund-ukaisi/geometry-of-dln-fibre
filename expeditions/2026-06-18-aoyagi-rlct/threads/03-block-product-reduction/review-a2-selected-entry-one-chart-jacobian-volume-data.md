# Review: A2 selected-entry one-chart Jacobian/volume data

Reviewer: Tesla the 4th, xhigh implementation review.

Verdict: PASS.  No findings.

## Scope

Reviewed the uncommitted checkpoint:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryChartPointMeasureBridge.lean
lean/DLNFibre/DLN/Aoyagi/SelectedEntryOneChartJacobianVolumeData.lean
lean/DLNFibre.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-selected-entry-one-chart-jacobian-volume-data.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-selected-entry-one-chart-jacobian-volume-data.md
```

## Findings

No findings.

## Checked Points

- The theorem
  `map_formalChartMap_chartPointProductMeasure_withDensity_eq_restrict_image`
  has the intended finite chart-point pushforward content and no positivity
  hypothesis.
- The proof follows the intended route: rewrite through
  `map_chartPointAdapter_withDensity_sourceDensity_eq_chartPointProductMeasure_withDensity`,
  then apply
  `map_formalChartMap_map_chartPointAdapter_weightedSignedBox_eq_restrict_image`.
- `selectedEntryOneChartAnalyticJacobianVolumeData` matches the existing
  `SelectedEntryAnalyticJacobianVolumeData` interface.  Positive radii are used
  for target nonemptiness and nonzero restricted source measure fields; the map
  equality uses the positivity-free pushforward theorem.
- The documentation states no citations for this checkpoint and keeps the
  deferred/nonclaim boundary explicit.

## Commands Reported By Reviewer

```text
git status --short
rg
git diff
nl -ba
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryChartPointMeasureBridge.lean
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryOneChartJacobianVolumeData.lean
lake env lean DLNFibre.lean
```

The first Lean invocation from the workspace root failed because the Lake
project root is `lean/`; rerunning from `lean/` passed.
