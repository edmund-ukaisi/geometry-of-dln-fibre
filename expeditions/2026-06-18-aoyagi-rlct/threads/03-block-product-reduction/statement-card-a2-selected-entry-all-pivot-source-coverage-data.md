# Statement card - A2 selected-entry all-pivot source coverage data

Date: 2026-06-29.

## Statement

For a nonempty finite selected-entry center and a supplied enumeration of all
center entries, the all-pivot selected-entry chart-family certificate has a
shared universal-domain context whose source domain is covered by the union of
the chart images.

Lean names:

```text
selectedEntryAllPivotAnalyticAtlasContext
selectedEntryAllPivotAnalyticSourceCoverageData
selectedEntryAllPivotAnalyticSourceCoverage
```

## Source reference

Aoyagi PDF pp. 15-22, where the displayed selected-entry blow-up chart uses

```text
x_p = u,
x_i = u r_i      for i != p.
```

The formal statement is expedition-built finite all-pivot coverage obtained by
varying the displayed selected-entry formula over possible pivots.  It is not a
claim that Aoyagi prints an all-pivot analytic atlas or supplies every analytic
atlas field.

## Dependencies

- `SelectedEntryAnalyticAtlasContext`
- `SelectedEntryAnalyticSourceCoverageData`
- `SelectedEntryAnalyticSourceCoverage`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`

## Nonclaims

This does not prove chart regularity, transition regularity, unit regularity,
Jacobian/volume compatibility, source production, branch termination,
normal-crossing extraction, pole order, or RLCT.  It also does not identify an
external/original source prior or construct the full
`SelectedEntrySuppliedAnalyticAtlasProducer`.

## Reproduction and review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-selected-entry-all-pivot-source-coverage-data.md
```

Review: pending.
Review:

```text
threads/03-block-product-reduction/review-a2-selected-entry-all-pivot-source-coverage-data.md
```

Verdict: PASS after source-scope documentation repair.
