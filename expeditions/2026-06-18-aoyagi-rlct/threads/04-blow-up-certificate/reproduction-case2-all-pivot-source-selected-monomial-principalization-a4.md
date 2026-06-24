# Reproduction - A4 Case 2 all-pivot source-selected monomial/principalization adapter

Date: 2026-06-24.

Status: finite selected-entry reproduction before Lean formalisation.

## Source Anchor

Aoyagi PDF pp. 19-21 uses the Case 2 residual-block center

```text
d_ij = 0,    J+1 <= i <= M(S),    J+1 <= j <= M^(S+1),
```

and writes the selected-entry chart at the displayed pivot `(J+1,J+1)`.
The all-pivot finite selected-entry family used in Lean is the same elementary
selected-entry construction over this finite center, with one chart for each
chosen pivot in the center.  This is a finite algebraic chart family, not a
claim that Aoyagi prints formulas for all non-displayed pivots.

## Reproduction

Let

```text
E = case2ResidualBlockPivotEntries n S J.
```

The all-pivot finite chart certificate enumerates charts by

```text
finsetSubtypeChartEquiv E : Fin E.card ~= E.
```

For chart `c`, write

```text
p_c = finsetSubtypeChartEquiv E c : E.
```

At the standard source point `(u, residual)`, the chart map is

```text
q |-> selectedEntryChartMap p_c.1 u residual q.
```

The source-selected Case 2 chart map for the supplied pivot membership
`p_c.2 : p_c.1 in E` is definitionally the same formula:

```text
case2SourceSelectedChartMapOfMem p_c.2 u residual q
  = selectedEntryChartMap p_c.1 u residual q.
```

Therefore the existing selected-entry calculations transport to the
source-selected names.

First, the finite residual-block center ideal is principalized by the selected
variable:

```text
span { case2SourceSelectedChartMapOfMem p_c.2 u residual q | q in E }
  = span {u}.
```

The inclusion `<=` holds because each selected-entry chart value is divisible
by `u`: at the pivot it is `u`, and off the pivot it is `u * residual q`.
The reverse inclusion holds because the pivot value itself is `u`.

Second, the selected-entry square-sum calculation gives

```text
sum_{q in E} (case2SourceSelectedChartMapOfMem p_c.2 u residual q)^2
  = u^2 * (1 + sum_{q in E \ {p_c}} residual(q)^2).
```

In the finite normal-crossing certificate this is recorded as the loss
monomial identity with the selected chart coordinate `u` and a unit factor

```text
selectedEntryCenterSqUnitFactor (E.erase p_c.1) residual.
```

Third, the formal pivot-first Jacobian matrix for the selected-entry
coordinate change has determinant

```text
u ^ card(E.erase p_c.1).
```

The finite certificate records this as the Jacobian/prior monomial identity.
This remains a formal selected-entry determinant calculation, not an analytic
volume-form theorem.

## Lean Targets

Add Case 2 source-selected adapters for the all-pivot finite certificate:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.centerIdeal_sourceSelectedChartMap_eq_span_singleton
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartPoint_eq_sourceSelectedCenterSq
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartPoint_eq_sourceSelectedUnitFactor
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartPoint_eq_sourceSelectedDet
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartPoint_sourceSelected
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartPoint_sourceSelected
```

## Boundary

- This is finite selected-entry algebra in source-selected names.
- It connects the all-pivot finite certificate's chart-level loss/Jacobian
  monomial fields to the existing source-selected Case 2 chart map.
- It does not prove that Aoyagi displays all non-top-left pivot charts.
- It does not produce successor matrices, suffix products, recurrence
  post-data, exponent post-data, analytic chart coverage, transition
  regularity, analytic Jacobian/volume control, normal crossings, pole order,
  or RLCT extraction.

## Kill Conditions

- Do not use this as an arbitrary-pivot source-production theorem.
- Do not treat finite center principalization as analytic normal crossings for
  the full DLN loss.
- Do not feed the local finite certificate into global A0 extraction without
  the missing chart coverage, unit, transition, and total-loss data.
