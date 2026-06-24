# Reproduction - A4 Case 2 chart-index Schur transition

Date: 2026-06-24.

Status: Lean formalised; focused/full build, sorry audit, whitespace check,
and independent xhigh review passed.

## Source Anchor

Aoyagi PDF pp. 20-21, Case 2.  The displayed computation normalises a selected
residual-block pivot, applies the elementary `Q` operation, and exposes the
lower-right Schur expression `D - x*y`.  The paper displays the top-left Case 2
pivot.  The all-pivot chart indices used here are the expedition's finite
selected-entry scaffold over supplied residual-block pivots; this note does not
claim that Aoyagi writes every non-top-left chart.

## Reproduction

Let `p` be a source selected pivot in the residual-block center and write the
normalised source chart coordinates as

```text
x_rs = selectedEntryNormalizedMap p residual (r,s).
```

Let the target pivot be `q = (a,b)`, with normalised source coordinate

```text
x_ab = selectedEntryNormalizedMap p residual q.
```

On the target overlap assume

```text
x_ab != 0.
```

The target selected-entry residual function is

```text
w_rs = x_rs / x_ab.
```

Thus `w_ab = 1`, and the target pivot-first lower-right Schur coordinate for
off-pivot row `i != a` and column `j != b` is

```text
z_ij
  = w_ij - w_ib*w_aj
  = x_ij/x_ab - (x_ib/x_ab)*(x_aj/x_ab).
```

Clearing denominators gives

```text
x_ab^2 * z_ij = x_ab*x_ij - x_ib*x_aj.
```

The supplied-pivot Lean wrapper is exactly this identity with
`case2SourceSelectedNormalizedMapOfMem` names.  The chart-indexed wrapper
chooses `p` and `q` from the finite all-pivot chart enumeration

```text
finsetSubtypeChartEquiv (case2ResidualBlockPivotEntries n S J).
```

The off-pivot row and column indices in these two wrappers are ambient
`ℕ` complements of the target row and column.  This is appropriate for the
total source-coordinate map used here.  A later theorem that needs residual-row
and residual-column subtype complements should add a separate adapter.

## Lean Targets

```text
case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_mul_sq
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_schurComplement_transition_mul_sq
```

The first theorem is a supplied-pivot Case 2 source-coordinate wrapper around
the generic denominator-cleared field identity.  The second is the chart-index
adapter for the all-pivot selected-entry certificate.

## Boundary

- This is finite source-coordinate matrix/field algebra only.
- It proves no analytic transition regularity, no open-neighbourhood gluing,
  no chart coverage, no source-displayed all-pivot atlas, no successor
  residual/following-factor production, no analytic Jacobian/volume theorem,
  no global normal crossings, no pole order, and no RLCT extraction.
- The denominator is the normalised coordinate `x_ab`, not the finite center
  value `u*x_ab`.
- The off-pivot indices are ambient source-coordinate complements, not a
  residual-block-domain restriction.

## Kill Conditions

- Do not use the theorem without the explicit nonzero denominator.
- Do not replace `x_ab != 0` by `u*x_ab != 0`.
- Do not treat the chart-indexed wrapper as source evidence that Aoyagi
  displayed all pivot charts.
- Do not treat the scalar Schur coordinate identity as full Case 2 successor
  production.
