# Reproduction - A2 selected-entry all-pivot source coverage data

Date: 2026-06-29.

Status: pen-and-paper reproduction before Lean.

## Question

The one-chart selected-entry context with universal source domain does not cover
all center values when the finite center has a non-pivot coordinate: every point
with selected coordinate zero maps to the origin.  Can the all-pivot
selected-entry chart family cover every finite center value, using the same
universal source and chart domains, without claiming the rest of the analytic
atlas producer?

## Source anchor

Aoyagi's selected-entry blow-up chart, used in the product-reduction/blow-up
step on PDF pp. 15-22, selects the displayed top-left center entry as the
exceptional coordinate and divides the other center entries by it.  The local
formula is

```text
x_p = u,
x_i = u r_i     for i != p.
```

The all-pivot family below is expedition-built finite data obtained by varying
this displayed selected-entry formula over possible pivots.  Aoyagi does not
print it as an analytic atlas or source-neighborhood theorem.  The calculation
below is only finite coordinate coverage.  It is not analytic transition
regularity, measure transport, source production for the recursive branch
state, branch termination, normal-crossing extraction, pole order, or RLCT.

## Calculation

Let `center` be a nonempty finite set and let `value : center -> R` be a center
value over a field `R`.

For a pivot `p`, the selected-entry chart map is

```text
chart_p(u, r)_p = u,
chart_p(u, r)_i = u r_i      for i != p.
```

There are two cases.

1. If `value_i = 0` for every `i`, choose any pivot `p`.  Take

```text
u = 0,
r_i = 0      for every i != p.
```

Then `chart_p(u,r)` is the zero center value, hence equals `value`.

2. Otherwise choose `p` with `value_p != 0`.  Take

```text
u = value_p,
r_i = value_i / value_p      for every i != p.
```

Then

```text
chart_p(u,r)_p = value_p,
chart_p(u,r)_i = value_p * (value_i / value_p) = value_i
```

for every `i != p`, because `value_p` is nonzero.  Thus
`chart_p(u,r) = value`.

Therefore the all-pivot selected-entry chart family covers every finite center
value:

```text
forall value, exists pivot chart point x, chartMap pivot x = value.
```

If we define a shared context for this finite chart family by

```text
sourceDomain = univ,
chartDomain pivot = univ,
chartTopology pivot = the product topology on the chart point type,
```

then the above finite coverage is exactly the field required by
`SelectedEntryAnalyticSourceCoverageData` for that shared context.

## Lean target

Add a narrow all-pivot source-coverage module with:

```text
selectedEntryAllPivotAnalyticAtlasContext
selectedEntryAllPivotAnalyticSourceCoverageData
selectedEntryAllPivotAnalyticSourceCoverage
```

The proof should reuse the existing finite theorem:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate
  .exists_chartPoint_chartMap_eq_value
```

## Kill conditions

- The context silently fixes only one pivot chart rather than the all-pivot
  chart family.
- The theorem claims chart regularity, transition regularity, unit regularity,
  Jacobian/volume compatibility, source production, branch termination,
  normal-crossing extraction, pole order, or RLCT.
- The proof uses the quiver paper or quiver Lean branch as evidence.
- The source domain or chart domains are not the same domains used in the
  stated `SelectedEntryAnalyticSourceCoverageData`.
