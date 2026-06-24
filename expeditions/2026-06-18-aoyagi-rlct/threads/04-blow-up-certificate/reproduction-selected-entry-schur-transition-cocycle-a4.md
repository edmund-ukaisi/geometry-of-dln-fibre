# Reproduction - A4 selected-entry Schur transition cocycle

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised and reviewed.

## Source Anchor

Aoyagi PDF pp. 20-21, Case 2, uses the selected-pivot `Q/P` calculation after
normalising a residual-block pivot.  This note records only the finite
selected-entry coordinate consequence obtained by combining that lower-right
Schur calculation with the already-reproduced selected-entry transition
cocycle.  It does not add any analytic transition, chart-coverage, or
successor-production claim.

## Reproduction

Let the source, middle, and target selected pivots be `p`, `q`, and `r`.  In
the source chart write normalized coordinates

```text
x_e = selectedEntryNormalizedMap p residual e,
x_p = 1.
```

Assume the source normalized coordinates of the middle and target pivots are
nonzero:

```text
x_q != 0,
x_r != 0.
```

The direct source-to-target transition uses

```text
z_e = x_e/x_r.
```

The source-to-middle transition uses

```text
y_e = x_e/x_q.
```

The middle target coordinate is

```text
y_r = x_r/x_q,
```

which is nonzero.  The middle-to-target transition therefore gives

```text
z'_e = y_e/y_r = (x_e/x_q)/(x_r/x_q) = x_e/x_r.
```

Thus the normalized target matrix used for the target pivot is the same by
the two routes:

```text
A'_ab = selectedEntryNormalizedMap r z' (a,b)
     = selectedEntryNormalizedMap r z  (a,b)
     = A_ab.
```

For target off-pivot row and column indices `i` and `j`, the lower-right
Schur entry used in the finite `Q/P` block is

```text
S_ij(A) = A_ij - A_i,rcol * A_rrow,j.
```

Since every target-normalized entry of `A'` equals the corresponding entry of
`A`, the Schur entries agree:

```text
S_ij(A') = S_ij(A).
```

This is not the denominator-cleared source formula

```text
x_r^2 * S_ij(A) = x_r*x_ij - x_i,rcol*x_rrow,j.
```

That formula was already formalised separately.  The new point is only that
the target Schur block is route-independent under the finite selected-entry
cocycle.

## Case 2 Specialization

For the Case 2 residual-block center

```text
E = case2ResidualBlockPivotEntries n S J,
```

the source, middle, and target pivots come from

```text
finsetSubtypeChartEquiv E sourceChart,
finsetSubtypeChartEquiv E middleChart,
finsetSubtypeChartEquiv E targetChart.
```

The target lower-right `Q/P` block should be stated with the residual-row and
residual-column subtype complements already used by

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_mul_sq.
```

## Lean Targets

Generic product-indexed finite algebra:

```text
selectedEntryNormalizedMap_schurComplement_transition_cocycle
```

Case 2 chart-indexed residual-block wrapper:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_cocycle
```

## Boundary

- This is finite selected-entry and `Q/P` residual-block coordinate algebra.
- It proves no analytic transition regularity, no open-neighbourhood gluing,
  no chart coverage, no source-displayed all-pivot atlas, no successor
  residual/following-factor production, no analytic Jacobian/volume theorem,
  no global normal crossings, no pole order, and no RLCT extraction.
- The nonzero hypotheses are normalized coordinates `x_q != 0` and `x_r != 0`,
  not finite center values `u*x_q` or `u*x_r`.
- The equality is target Schur-entry equality, not source production of a
  successor residual matrix or following factor.

## Kill Conditions

- Do not replace normalized-coordinate nonzero hypotheses by nonzero finite
  center values.
- Do not state analytic regularity, chart coverage, or open gluing.
- Do not identify this route-independence theorem with the denominator-cleared
  source Schur formula; it is a compatibility theorem for the target Schur
  block after the target normalized coordinates have already been constructed.
- Do not treat this scalar lower-right block equality as full Case 2 successor
  production, chart coverage, or transition regularity.
