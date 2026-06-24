# Reproduction - A4 Case 2 all-pivot source-selected chart adapter

Date: 2026-06-24.

Status: checked finite selected-entry chart-coordinate reproduction.

## Source Anchor

Aoyagi PDF pp. 19-21 uses the Case 2 residual-block center

```text
d_ij = 0,    J+1 <= i <= M(S),    J+1 <= j <= M^(S+1),
```

and displays the selected-entry chart at the top-left residual pivot
`(J+1,J+1)`.  The all-pivot selected-entry certificate is the standard finite
chart family over this same finite center: one chart for each selected center
coordinate.  Aoyagi explicitly displays only the top-left chart; the all-pivot
family is the usual selected-entry finite chart family over the printed center,
not a claim that the paper prints every chart.

## Reproduction

Let

```text
E = case2ResidualBlockPivotEntries n S J.
```

The all-pivot finite certificate enumerates charts by an equivalence

```text
finsetSubtypeChartEquiv E : Fin E.card ~= E.
```

For a chart index `c`, write

```text
p_c = finsetSubtypeChartEquiv E c : E.
```

The generic selected-entry source point in chart `c` has coordinates

```text
(u, residual),
```

and its chart map is the standard selected-entry formula

```text
q |-> selectedEntryChartMap p_c.1 u residual q.
```

The source-selected Case 2 map for a supplied residual-block pivot is defined
by the same formula, with the pivot membership proof retained:

```text
case2SourceSelectedChartMapOfMem p_c.2 u residual q
  = selectedEntryChartMap p_c.1 u residual q.
```

Therefore the all-pivot finite certificate chart map at this source point is
exactly the source-selected Case 2 chart map for the pivot selected by `c`.

## Lean Targets

Lean records the concrete selected-entry chart-family adapter:

```text
Case2ResidualBlockSelectedEntryChartFamilyData.standard_value_eq_sourceSelectedChartMapOfMem
```

and the all-pivot certificate source-point adapter:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartPoint_eq_sourceSelectedChartMapOfMem
```

## Boundary

- This is finite selected-entry chart-coordinate algebra only.
- It connects the all-pivot finite certificate to the existing supplied-pivot
  source-selected Case 2 map.
- It does not prove that Aoyagi displays every non-top-left pivot chart.
- It does not produce successor matrices, suffix products, recurrence
  post-data, exponent post-data, chart coverage, transition regularity,
  Jacobian or volume-form control, normal crossings, pole order, or RLCT.

## Kill Conditions

- Do not cite this as a source-production theorem for `C'^(S+1)`.
- Do not use it to bypass the separate arbitrary-pivot source-production
  frontier.
- Do not treat finite selected-entry chart-family coverage as analytic atlas
  coverage.
