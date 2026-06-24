# Reproduction - A4 selected-entry transition inverse

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised and gated.

## Source Anchor

Aoyagi PDF pp. 20-21, Case 2, uses the elementary selected-pivot coordinate
change before the displayed `Q/P` lower-right Schur block.  The paper displays
the top-left pivot, so this note records only the finite selected-entry
coordinate algebra reconstructed from that displayed chart.  It does not claim
that Aoyagi prints every pivot chart or analytic transition map.

## Reproduction

Let `p` be the source selected pivot and `q` the target selected pivot.  In the
source chart write the center values as

```text
d_e = u*x_e,
```

where

```text
x_e = selectedEntryNormalizedMap p residual e,
x_p = 1.
```

On the target overlap assume

```text
x_q != 0.
```

The source-to-target transition uses

```text
u_q = u*x_q,
y_e = x_e/x_q.
```

The normalized target-coordinate formula is

```text
selectedEntryNormalizedMap q y e = x_e/x_q.
```

For `e = q`, both sides are `1`.  For `e != q`, this is the definition of the
target residual coordinate.

To invert the transition, the source pivot has target-normalized coordinate

```text
y_p = x_p/x_q = 1/x_q.
```

The reverse transition therefore uses selected variable

```text
u_p' = u_q*y_p = (u*x_q)*(1/x_q) = u,
```

and reverse residual coordinates

```text
z_e = y_e/y_p = (x_e/x_q)/(1/x_q) = x_e.
```

On the source chart point, residuals are stored only away from `p`; there
`x_e = residual(e)`.  Thus the reverse transition returns the same chart point.

## Case 2 Specialization

For the Case 2 residual-block center

```text
E = case2ResidualBlockPivotEntries n S J,
```

the source and target pivots are supplied by

```text
finsetSubtypeChartEquiv E sourceChart,
finsetSubtypeChartEquiv E targetChart.
```

The same normalized-coordinate inverse applies with
`case2SourceSelectedNormalizedMapOfMem` in place of
`selectedEntryNormalizedMap`.

## Lean Targets

Generic finite algebra:

```text
selectedEntryNormalizedMap_transition_eq_div_of_target_normalized_ne_zero
```

Generic selected-entry chart family:

```text
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_self
selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero
```

Case 2 all-pivot residual-block certificate:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_self
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero
```

## Boundary

- This is finite selected-entry coordinate algebra.
- It proves no analytic transition regularity, no chart coverage, no
  open-neighbourhood gluing, no source-displayed all-pivot atlas, no
  successor residual/following-factor production, no analytic Jacobian/volume
  theorem, no global normal crossings, no pole order, and no RLCT extraction.
- The nonzero denominator is the normalized coordinate `x_q`, not the finite
  center value `u*x_q`.
- The inverse theorem is a chart-point identity, not equality of arbitrary raw
  ambient residual functions.  Raw residual values at the selected pivot are
  intentionally irrelevant.

## Kill Conditions

- Do not replace `x_q != 0` by `u*x_q != 0`.
- Do not claim analytic regularity, open gluing, or coverage from this finite
  inverse law.
- Do not state equality of raw ambient residual functions; use normalized maps
  or chart points.
- Do not use this to repair the separate printed-vector mismatch or p. 21
  extra-`u` ambiguity.
