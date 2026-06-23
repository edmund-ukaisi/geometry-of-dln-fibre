# Reproduction - Case 2 source-chart selected-entry microcertificate adapter

Date: 2026-06-23.

Status: reproduced, formalised, and independently reviewed.

## Source Boundary

Aoyagi PDF p. 5 uses the sum of squares of local generators as the local loss
convention.  PDF p. 6 reads finite normal-crossing exponent data from a
monomial loss and monomial Jacobian/prior display.  In the continuing Case 2
chart on PDF pp. 19-22, the displayed selected-entry substitution is

```text
d_(J+1,J+1) = u,
d_(i,j) = u d'_(i,j)    for all other residual-block center entries.
```

Earlier A4 slices already reproduced the center-square factorization and the
formal pivot-first determinant.  The selected-entry microcertificate already
packages the abstract finite selected-entry chart as a one-chart
`AoyagiNormalCrossingChartCertificate`.  This slice only identifies the
abstract microcertificate's chart point with the concrete displayed Case 2
source chart point.

## Pen-and-Paper Calculation

Let

```text
E = case2ResidualBlockPivotEntries n S J,
p = (J+1,J+1),
E' = E \ {p}.
```

The abstract selected-entry microcertificate uses chart coordinates

```text
(u, y_e)_{e in E'}
```

and sends them to a finite-center value function

```text
x_p = u,
x_e = u y_e.
```

The concrete displayed Case 2 source chart uses the same formulas with
`y_e = residual e`.  Therefore the abstract chart map at the source chart
point is pointwise the displayed source chart map:

```text
chartMap(sourcePoint)(e) = case2DisplayedSourceChartMap n hS hcont u residual e.
```

Consequently the abstract certificate's loss at that chart point is exactly
the concrete residual-center square-sum:

```text
loss(chartMap(sourcePoint))
  = selectedEntryCenterSq E (case2DisplayedSourceChartMap n hS hcont u residual).
```

Its loss unit is the normalized square-sum factor

```text
selectedEntryCenterSqUnitFactor E' residual,
```

and its Jacobian/prior field is

```text
u ^ |E'|.
```

The existing formal determinant calculation gives

```text
det(selectedEntryPivotFirstJacobian (kappa := E') u (fun e => residual e.1))
  = u ^ |E'|,
```

so the certificate's Jacobian/prior value agrees with the formal pivot-first
determinant at the source chart point.

This is a presentation adapter.  It does not add chart coverage, source
production, transition regularity, analytic neighbourhood control, a true
volume-form theorem, total DLN loss control, pole order, or RLCT extraction.

## Lean Target

Add source-point evaluation lemmas in

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

expected names:

```text
case2DisplayedCenterSqFormalJacobianChartCertificate.sourceChartPoint
case2DisplayedCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq
case2DisplayedCenterSqFormalJacobianChartCertificate.loss_sourceChartPoint_eq_centerSq
case2DisplayedCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq
case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPrior_sourceChartPoint_eq_det
case2DisplayedCenterSqFormalJacobianChartCertificate.loss_monomial_sourceChartPoint
case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPrior_monomial_sourceChartPoint
```

## Boundary

- No global A0 normal-crossing chart family.
- No proof that the displayed chart covers a neighbourhood.
- No source production of successor or suffix data.
- No analytic unit neighbourhood theorem.
- No analytic Jacobian, derivative, or volume-form theorem.
- No total DLN loss monomial identity.
- No active-ratio lower bound or chart-count theorem.
- No pole order or RLCT extraction.

## Kill Conditions

- If the adapter requires an arbitrary supplied `Cnc` or `D`, it is only
  another consumer and should not be counted as source-moving progress.
- If the theorem uses the local finite center square-sum as the total DLN
  loss, it overclaims.
- If the formal determinant is advertised as an analytic Jacobian theorem, it
  overclaims.
