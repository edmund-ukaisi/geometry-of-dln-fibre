# Review: A2 selected-entry one-chart analytic predicate data

Reviewers: Lorentz the 4th, xhigh source/scope review; Harvey the 4th, xhigh
Lean/API review.

Verdict: PASS.  No findings.

## Scope

Reviewed the uncommitted checkpoint:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryOneChartAnalyticPredicateData.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-selected-entry-one-chart-analytic-predicate-data.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-selected-entry-one-chart-analytic-predicate-data.md
```

## Findings

No findings.

## Checked Points

- The four theorems only witness the forgetful predicates
  `exists ctx, Nonempty (data ctx)`.
- The shared witness context is
  `selectedEntryOneChartAnalyticAtlasContext pivot`.
- The Jacobian/volume-compatible predicate keeps the positive-radii input
  required by `selectedEntryOneChartAnalyticJacobianVolumeData`.
- No `SelectedEntryAnalyticSourceCoverage` theorem is produced; in particular,
  `sourceDomain = Set.univ` in the one-chart context is not treated as source
  coverage.
- No paper-source citation beyond the already reproduced finite selected-entry
  substitution and Jacobian-density context is involved.
- The nonclaim boundary is preserved: no source-domain coverage, full supplied
  analytic atlas producer, source production, branch termination, source-prior
  transport, determinant-chart Haar theorem, source-rank coverage,
  normal-crossing extraction, pole order, or RLCT.

## Commands Reported By Reviewers

```text
lake env lean --stdin
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryOneChartAnalyticPredicateData.lean
```

The Lean/API reviewer also checked the theorem names by `#check`.  All probes
passed from the `lean/` Lake root.
