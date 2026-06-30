# A2 selected-entry one-chart source-coverage obstruction

## Scope

This note records the elementary obstruction to source coverage for the exact
one-chart context:

```text
selectedEntryOneChartAnalyticAtlasContext pivot
```

That context has `sourceDomain = univ` and one chart domain `univ`.  The
selected-entry chart is:

```text
x_p = u,
x_i = u r_i  for i != p.
```

The result is only a negative statement about this exact one-chart universal
source-domain context.  It is not a statement about a smaller source domain, a
multi-pivot atlas, or a separately supplied analytic atlas producer.

## Obstruction

Assume the finite center contains a non-pivot coordinate `q != p`.

Define a source-domain point `v : center -> R` by:

```text
v_p = 0,
v_q = 1,
v_i = 0  otherwise.
```

Since the one-chart context has `sourceDomain = univ`, this point lies in the
source domain.

If it were in the image of the one selected-entry chart, then for some chart
point `(u, r)` we would have:

```text
v_p = u.
```

But `v_p = 0`, so `u = 0`.  Then every non-pivot output coordinate is:

```text
x_i = u r_i = 0.
```

In particular `v_q` would be `0`, contradicting `v_q = 1`.

Therefore:

```text
not SelectedEntryAnalyticSourceCoverageData
  (selectedEntryOneChartAnalyticAtlasContext pivot)
```

whenever a non-pivot coordinate exists.

## Lean Names

```text
formalChartMap_pivot
formalChartMap_eq_zero_of_fst_eq_zero
not_selectedEntryOneChartAnalyticSourceCoverageData_of_ne
```

## Kill Conditions

- Kill if this is used to rule out source coverage for a smaller source
  domain.
- Kill if this is used to rule out source coverage for a multi-pivot atlas.
- Kill if this is used to rule out a separately supplied analytic atlas
  producer.
- Kill if this is used as a source-production, branch-termination,
  source-prior, determinant-chart Haar, source-rank coverage,
  normal-crossing extraction, pole-order, or RLCT theorem.
