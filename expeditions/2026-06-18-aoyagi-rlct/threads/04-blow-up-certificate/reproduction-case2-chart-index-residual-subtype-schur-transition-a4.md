# Reproduction - A4 Case 2 chart-index residual-subtype Schur transition

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised and gated.

## Source Anchor

Aoyagi PDF pp. 20-21, Case 2.  The displayed selected-pivot `Q/P`
calculation normalises one residual-block pivot and exposes the lower-right
Schur expression `D - x*y`.  This note does not add a new source claim: it
combines the already-reproduced denominator-cleared Schur formula with the
residual-row and residual-column subtype indices used by the target lower-right
`Q/P` block.

## Reproduction

Let the Case 2 residual-block center be

```text
E = case2ResidualBlockPivotEntries n S J.
```

The all-pivot selected-entry chart family enumerates pivots by

```text
finsetSubtypeChartEquiv E : Fin E.card ~= E.
```

For source and target chart indices, write

```text
p = sourcePivot,
q = targetPivot = (a,b).
```

In the source selected chart, set

```text
x_rs = case2SourceSelectedNormalizedMapOfMem p_mem residual (r,s).
```

On the target overlap, assume the normalized target coordinate is nonzero:

```text
x_ab != 0.
```

The target residual function is

```text
w_rs = x_rs / x_ab.
```

For the target lower-right `Q/P` block, the off-pivot row and column indices
are not merely ambient complements.  They are subtype complements

```lean
i : pivotComplement (case2ResidualBlockPivotRowOfMem q_mem)
j : pivotComplement (case2ResidualBlockPivotColOfMem q_mem).
```

Their ambient source labels are `i.1.1` and `j.1.1`.  The target Schur
coordinate in the residual-block subtype matrix is

```text
z_ij = w_(i,j) - w_(i,b)*w_(a,j),
```

where `i` and `j` are read through those ambient labels.  Clearing
denominators gives

```text
x_ab^2 * z_ij
  = x_ab*x_(i,j) - x_(i,b)*x_(a,j).
```

This is exactly the residual-subtype Schur identity, with `p` and `q` supplied
by the chart enumeration rather than as separate membership arguments.

## Lean Target

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_mul_sq
```

The theorem should be a chart-index wrapper over

```text
case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq.
```

## Boundary

- This is finite selected-entry and `Q/P` residual-block coordinate algebra.
- It proves no analytic transition regularity, no open-neighbourhood gluing,
  no chart coverage, no source-displayed all-pivot atlas, no successor
  residual/following-factor production, no analytic Jacobian/volume theorem,
  no global normal crossings, no pole order, and no RLCT extraction.
- The denominator is the normalized coordinate `x_ab`, not the finite center
  value `u*x_ab`.
- The off-pivot indices are residual-block subtype complements, not a proof of
  source-produced successor residual coordinates.

## Kill Conditions

- Do not use the theorem without the explicit nonzero denominator.
- Do not replace `x_ab != 0` by `u*x_ab != 0`.
- Do not treat the chart-indexed residual-subtype wrapper as source evidence
  that Aoyagi displayed all pivot charts.
- Do not treat this scalar lower-right block formula as full Case 2 successor
  production, chart coverage, or transition regularity.
