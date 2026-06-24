# Reproduction - A4 selected-entry source-point coverage with coordinate

Date: 2026-06-24.

Status: reproduced; Lean target selected.

## Source Anchor

Aoyagi's Case 1 and Case 2 blow-up charts on PDF pp. 15-18 use the usual
selected-entry affine charts for a finite center.  If the center coordinates
are indexed by a finite set `E` and `p in E` is the chosen pivot, the affine
chart has coordinates

```text
x_p = u,
x_i = u y_i  for i != p.
```

For Case 1, the finite center consists of the old exceptional variable token
and the selected row-strip entries.  Aoyagi prints the old-variable chart and
the representative selected-entry pivot chart.  The all-pivot Lean family is
the finite formal generalization: one chart for every finite center generator,
including the old token and every selected row-strip entry.

For Case 2, the same selected-entry formula is used for the residual-block
center; again Lean carries the all-pivot finite family.

## Finite Source-Point Coverage

Let `value : E -> K` be a finite center value.

If some coordinate `value p` is nonzero, choose that pivot.  Set

```text
u = value p,
y_i = value i / value p  for i != p.
```

Then the selected-entry chart map recovers `value`, because

```text
u = value p,
u y_i = value p * (value i / value p) = value i.
```

If all coordinates of `value` are zero, choose any pivot and set

```text
u = 0,
y_i = 0.
```

The chart map again recovers `value`.

The existing Lean finite coverage theorem already packages this as a source
chart point `(u, residual)`.  This slice only records, in the same
existential package, the coordinate projection

```text
coord(..., sourceChartPoint c u residual, 0) = u.
```

This coordinate equality is definitional for the selected-entry certificate:
the unique certificate coordinate is the exceptional selected variable.

## Case 1 Specialization

For the Case 1 all-pivot center

```text
case1CenterGenerators n S J J1,
```

the old exceptional generator supplies nonemptiness.  Therefore every finite
Case 1 center value has a chart index `c`, selected variable `u`, and residual
function such that the Case 1 all-pivot finite chart map recovers the value
and the unique certificate coordinate is `u`.

This statement is source-facing finite chart-map bookkeeping.  It does not say
that Aoyagi prints every selected row-strip pivot chart, only that the finite
selected-entry construction used in Lean includes all analogous pivot charts.

After independent review, the Lean implementation keeps only the generic
source-point/coordinate theorem in this slice.  A Case 1 wrapper is a thin
specialization of the generic theorem and should be added only when a
downstream Case 1 theorem directly consumes it.

## Boundary

This is finite chart-map and coordinate bookkeeping only.

- no analytic chart domains or neighbourhood coverage;
- no transition regularity;
- no source production of successor matrices, suffix products, or recurrence
  post-data;
- no analytic Jacobian or volume-form theorem;
- no global normal-crossing certificate;
- no termination, pole order, or RLCT extraction.

## Kill Conditions

- Do not use the word coverage without the qualifier finite chart-map/source
  point coverage.
- Do not use the theorem as an analytic atlas coverage field.
- Do not infer source production or transition regularity from the existence
  of a finite source chart point.
