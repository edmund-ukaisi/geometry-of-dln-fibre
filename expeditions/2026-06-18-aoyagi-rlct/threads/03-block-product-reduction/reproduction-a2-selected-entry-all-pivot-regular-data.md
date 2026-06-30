# Reproduction - A2 selected-entry all-pivot regular data

Date: 2026-06-29.

Status: pen-and-paper reproduction before Lean.

## Question

The all-pivot selected-entry chart family already has a shared universal
source/chart-domain context and source coverage.  Can the one-chart continuity
and unit facts be lifted to chart regularity and unit regularity for that same
all-pivot context?

Answer: yes.  This is chart-by-chart bookkeeping.  It does not construct
transition maps between different pivots, a volume/Jacobian theorem, branch
source production, termination, normal crossings, pole order, or RLCT.

## Calculation

Let `center` be a nonempty finite set and let

```text
chartEquiv : Fin center.card ~= center
```

enumerate its possible selected pivots.  The all-pivot certificate has one
chart for each `c : Fin center.card`.  The chart indexed by `c` is
definitionally the one-pivot selected-entry certificate at

```text
p = chartEquiv c.
```

Its chart point is

```text
(u, r) : R x ((center.erase p) -> R),
```

and its chart map is

```text
x_p = u,
x_i = u r_i       for i != p.
```

Over `R = Real`, each coordinate of the chart map is continuous:

```text
x_p(u,r) = u
x_i(u,r) = u * r_i.
```

The unique normal-crossing coordinate is also continuous:

```text
coord(u,r) = u.
```

The loss unit is

```text
1 + sum_{i != p} r_i^2,
```

hence continuous and strictly positive, so it is a unit in `Real`.  The formal
Jacobian/prior unit is the constant `1`, hence continuous and a unit.

The existing one-chart file already proves these facts as:

```text
continuous_formalChartMap
continuous_chartPointCoord
continuous_chartPointLossUnit
continuous_chartPointJacobianPriorUnit
selectedEntryOneChartAnalyticChartRegularData
selectedEntryOneChartAnalyticUnitRegularData
```

For the all-pivot context, the proof is to apply these one-chart facts to
`chartEquiv c` for every chart `c`.

## Lean target

Add a narrow all-pivot regularity module with:

```text
selectedEntryAllPivotAnalyticChartRegularData
selectedEntryAllPivotAnalyticUnitRegularData
selectedEntryAllPivotAnalyticChartRegular
selectedEntryAllPivotAnalyticUnitRegular
```

The shared context must be exactly:

```text
selectedEntryAllPivotAnalyticAtlasContext hcenter chartEquiv
```

## Kill conditions

- Do not claim transition regularity between distinct selected pivots.
- Do not claim Jacobian/volume compatibility for the all-pivot family.
- Do not claim source production, branch termination, normal-crossing
  extraction, pole order, or RLCT.
- Do not silently switch to the one-chart context; the data must use the
  all-pivot shared context.
