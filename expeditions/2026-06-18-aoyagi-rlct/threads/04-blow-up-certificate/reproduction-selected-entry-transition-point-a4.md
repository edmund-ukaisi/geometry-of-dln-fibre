# Reproduction - A4 selected-entry transition point

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised and gated.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2, says to construct the blow-up of the finite
residual-block center and displays the selected-entry chart at the top-left
residual pivot.  The displayed chart justifies reconstructing the standard
selected-entry affine charts for the finite center, but not treating every
chart or transition as explicitly printed by Aoyagi.

This note proves only the elementary finite overlap map for selected-entry
charts.  It is a step toward a concrete finite atlas interface, not a source
production theorem for the successor following object.

## Reproduction

Let `E` be a finite center and let `p,q in E` be source and target selected
pivots.  In the source chart, write the center values as

```text
d_e = u*x_e,
```

where

```text
x_p = 1,
x_e = residual(e)    for e != p.
```

Equivalently,

```text
x_e = selectedEntryNormalizedMap p residual e.
```

On the source-chart overlap where the target normalized coordinate is nonzero,

```text
x_q != 0,
```

define the target chart point by

```text
u_q = u*x_q,
y_e = x_e/x_q.
```

Then the target pivot is normalized:

```text
y_q = x_q/x_q = 1.
```

For every center coordinate,

```text
u_q*y_e = (u*x_q)*(x_e/x_q) = u*x_e = d_e.
```

Thus the target chart map at the constructed target point gives the same
finite center value as the source chart map at the original source point.
The load-bearing nonzero hypothesis is `x_q != 0`; it is not `u*x_q != 0`.

## Case 2 Specialization

For the Case 2 residual-block center

```text
E = case2ResidualBlockPivotEntries n S J,
```

the chart indices are enumerated by

```text
finsetSubtypeChartEquiv E : Fin E.card ~= E.
```

Given source and target chart indices `sourceChart` and `targetChart`, the
same construction uses

```text
p = (finsetSubtypeChartEquiv E sourceChart).1,
q = (finsetSubtypeChartEquiv E targetChart).1.
```

The target chart point is the finite point with selected variable

```text
u * case2SourceSelectedNormalizedMapOfMem p_mem residual q
```

and residual function

```text
r |-> case2SourceSelectedNormalizedMapOfMem p_mem residual r
      / case2SourceSelectedNormalizedMapOfMem p_mem residual q.
```

Under the normalized nonzero denominator hypothesis, its chart map is equal to
the source chart map of `sourceChart`.

## Lean Targets

Generic selected-entry family:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
```

Case 2 all-pivot residual-block certificate:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero
```

## Boundary

- This is finite selected-entry transition-point algebra.
- It constructs a target chart point and proves equality of finite chart maps
  on the normalized overlap.
- It does not prove analytic chart coverage, open-neighbourhood gluing,
  analytic transition regularity, Jacobian/volume-form control, normal
  crossings, pole order, or RLCT extraction.
- It does not source-produce `Csucc`, `C'^(S+1)`, suffix products, branchwise
  terminal objects, recurrence post-data, or exponent post-data.
- It does not say that Aoyagi printed every non-top-left pivot chart.

## Kill Conditions

- Do not replace `x_q != 0` by `u*x_q != 0`.
- Do not fill `ChartRegular` or `TransitionRegular` with `True` and call that
  chart regularity.
- Do not identify this finite transition-point equality with source
  production of the successor following object.
- Do not use it to repair the printed Case 2 vector mismatch or the p. 21
  extra-`u` ambiguity.
