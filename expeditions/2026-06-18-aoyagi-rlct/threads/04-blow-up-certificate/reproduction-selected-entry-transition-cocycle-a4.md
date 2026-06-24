# Reproduction - A4 selected-entry transition cocycle

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised and reviewed.

## Source Anchor

Aoyagi PDF pp. 20-21, Case 2, uses the elementary selected-pivot coordinate
change before the displayed `Q/P` calculation.  This note records only the
finite selected-entry coordinate algebra reconstructed from that displayed
chart.  It does not claim that Aoyagi prints every pivot chart or any analytic
transition map.

## Reproduction

Let `p`, `q`, and `r` be source, middle, and target selected pivots.  In the
source chart write

```text
d_e = u*x_e,
x_e = selectedEntryNormalizedMap p residual e,
x_p = 1.
```

Assume the middle and target normalized coordinates in the source chart are
nonzero:

```text
x_q != 0,
x_r != 0.
```

The direct source-to-target transition uses

```text
u_r = u*x_r,
z_e = x_e/x_r.
```

The source-to-middle transition uses

```text
u_q = u*x_q,
y_e = x_e/x_q.
```

In the middle chart, the target normalized coordinate is

```text
y_r = x_r/x_q,
```

which is nonzero because both `x_r` and `x_q` are nonzero.  The middle-to-target
transition then gives

```text
u_r' = u_q*y_r = (u*x_q)*(x_r/x_q) = u*x_r,
z_e' = y_e/y_r = (x_e/x_q)/(x_r/x_q) = x_e/x_r.
```

Thus the two-step transition `p -> q -> r` returns the same target chart point
as the direct transition `p -> r`.

The proof must be chart-point level, not raw ambient residual-function equality:
the target chart stores residuals only away from `r`, and raw ambient values at
the selected target pivot are intentionally irrelevant.

## Case 2 Specialization

For the Case 2 residual-block center

```text
E = case2ResidualBlockPivotEntries n S J,
```

the source, middle, and target pivots are obtained from

```text
finsetSubtypeChartEquiv E sourceChart,
finsetSubtypeChartEquiv E middleChart,
finsetSubtypeChartEquiv E targetChart.
```

The same cocycle law applies with `case2SourceSelectedNormalizedMapOfMem` in
place of `selectedEntryNormalizedMap`.

## Lean Targets

Generic finite algebra:

```text
selectedEntryNormalizedMap_transition_target_ne_zero_of_source_ne_zero
selectedEntryNormalizedMap_transition_transition_eq_div_of_ne_zero
```

Generic selected-entry chart family:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero
```

Case 2 all-pivot residual-block certificate:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero
```

## Boundary

- This is finite selected-entry coordinate algebra.
- It proves no analytic transition regularity, no chart coverage, no
  open-neighbourhood gluing, no source-displayed all-pivot atlas, no successor
  residual/following-factor production, no analytic Jacobian/volume theorem,
  no global normal crossings, no pole order, and no RLCT extraction.
- The nonzero hypotheses are normalized coordinates `x_q != 0` and `x_r != 0`,
  not finite center values `u*x_q` or `u*x_r`.
- The cocycle theorem is a chart-point identity, not equality of arbitrary raw
  ambient residual functions.

## Kill Conditions

- Do not replace normalized-coordinate nonzero hypotheses by nonzero finite
  center values.
- Do not assert analytic regularity, open gluing, or coverage from this finite
  cocycle law.
- Do not state equality of raw ambient residual functions; use normalized maps
  or chart points.
- Do not use this to repair the separate printed-vector mismatch or p. 21
  extra-`u` ambiguity.
