# Review: A2 selected-entry one-chart source-coverage obstruction

Reviewers: Epicurus the 4th, xhigh source/scope review; Nietzsche the 4th,
xhigh Lean/API review.

Verdict: PASS.  No findings.

## Scope

Reviewed the uncommitted checkpoint:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryOneChartSourceCoverageObstruction.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-selected-entry-one-chart-source-coverage-obstruction.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-selected-entry-one-chart-source-coverage-obstruction.md
```

## Findings

No findings.

## Checked Points

- The theorem is an Aoyagi-only elementary selected-entry chart calculation:
  it uses only the substitution `x_p = u`, `x_i = u r_i`.
- The obstruction is only for the exact context
  `selectedEntryOneChartAnalyticAtlasContext pivot`, where
  `sourceDomain = Set.univ` and there is only one pivot chart.
- The theorem proves only
  `¬ SelectedEntryAnalyticSourceCoverageData
    (selectedEntryOneChartAnalyticAtlasContext pivot)`.
- It does not prove `¬ SelectedEntryAnalyticSourceCoverage ...`, because that
  existential may choose another context.
- It does not rule out smaller source domains, multi-pivot atlases, or
  separately supplied analytic atlas producers.
- The nonclaim boundary remains explicit: no source production, branch
  termination, source-prior transport, determinant-chart Haar theorem,
  source-rank coverage, normal-crossing extraction, pole order, or RLCT.

## Commands Reported By Reviewer

```text
lake env lean --stdin
```

The Lean/API reviewer independently checked the exact proof route from the
`lean/` Lake root.
