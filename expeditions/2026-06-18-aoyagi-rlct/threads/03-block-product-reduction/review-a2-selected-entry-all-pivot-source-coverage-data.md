# Review - A2 selected-entry all-pivot source coverage data

Date: 2026-06-29.

## Verdict

PASS after source-scope documentation repair.

## Scope Reviewed

Lean:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotSourceCoverageData.lean
lean/DLNFibre.lean
```

Artifacts:

```text
reproduction-a2-selected-entry-all-pivot-source-coverage-data.md
statement-card-a2-selected-entry-all-pivot-source-coverage-data.md
```

## Source/Scope Review

Reviewer: Wegener the 4th, xhigh.

Initial verdict: FAIL for documentation scope only.  The first reproduction
and statement-card draft made the all-pivot family sound like it was supplied
by Aoyagi.  The repair now states that Aoyagi prints the displayed
selected-entry chart and that the all-pivot family is expedition-built finite
data obtained by varying that formula, not a source-stated analytic atlas.

Final verdict: PASS.  No remaining source/scope findings.

The theorem is accepted as narrow finite coordinate coverage for the all-pivot
certificate.  It is not a claim that Aoyagi prints an all-pivot analytic atlas.

## Lean/API Review

Reviewer: Nash the 4th, xhigh.

Verdict: PASS.  No actionable findings.

The context uses the standard product topology for the chart point type after
unfolding the finite certificate chart point.  The coverage data is
non-vacuous: source domain is `Set.univ`, and the coverage field uses the
existing finite all-pivot theorem
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.
The wrapper only packages this data into the forgetful
`SelectedEntryAnalyticSourceCoverage` predicate, not a full supplied analytic
atlas producer.

Nash independently checked:

```text
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryAllPivotSourceCoverageData.lean
lake env lean DLNFibre.lean
```

Both passed.  Axiom probes on the new declarations and the invoked coverage
theorem reported only `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

No chart regularity, transition regularity, unit regularity,
Jacobian/volume compatibility, full supplied analytic atlas producer, source
production, branch termination, original/source-prior transport,
determinant-chart Haar theorem, normal-crossing extraction, pole order, or
RLCT.
