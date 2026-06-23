# Reproduction - Case 1 source-chart selected-entry microcertificate adapter

Date: 2026-06-23.

Status: reproduced and formalised; independent review pending.

## Source Boundary

Aoyagi PDF p. 5 uses the local sum of squares of generators as the loss
convention.  PDF p. 6 reads finite exponent data from a monomial loss and
monomial Jacobian/prior display.  In the Case 1 charts on PDF pp. 17-18, the
finite center is the old selected generator together with the displayed
row-strip entries, and a selected-entry chart has the elementary form

```text
x_p = u,
x_e = u y_e    for e != p.
```

This slice does not reproduce source production of the old selected label,
chart coverage, transition regularity, or an analytic Jacobian theorem.  It
only identifies the finite selected-entry source coordinates inside the
existing one-chart `AoyagiNormalCrossingChartCertificate`.

## Pen-and-Paper Calculation

Let `E` be a finite center, let `p in E`, and let `E' = E \ {p}`.  The generic
selected-entry microcertificate has chart coordinates

```text
(u, y_e)_{e in E'}
```

and chart map

```text
x_p = u,
x_e = u y_e.
```

Given an ambient residual function `residual : E_ambient -> K`, the source
chart point is

```text
(u, residual|_{E'}).
```

At this point, the chart map is pointwise the ambient selected-entry chart
map, so the certificate loss is the finite center square-sum

```text
sum_{e in E} x_e^2.
```

The selected-entry factorization gives

```text
sum_{e in E} x_e^2
  = u^2 * (1 + sum_{e in E'} residual_e^2).
```

Thus the loss unit is the normalized finite square-sum factor

```text
1 + sum_{e in E'} residual_e^2.
```

The formal pivot-first determinant is the determinant of

```text
[ 1  0 ]
[ y  uI]
```

and therefore equals

```text
u ^ |E'|.
```

For Case 1 selected-old, `p` is the finite `Unit` token
`Sum.inl ()`.  For Case 1 displayed row-strip, `p` is the displayed
`Sum.inr (J+1,J+1)` generator.  In both cases Lean already proves

```text
|E'| = J1 * (n(S+1)-J).
```

The calculation is identical for the two pivots; the source interpretation is
not identical.  The `Unit` token remains tied to source data only through the
separate selected-old boundary.

## Lean Target

Add generic selected-entry source-point lemmas in

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

under

```text
selectedEntryCenterSqFormalJacobianChartCertificate
```

with names:

```text
sourceChartPoint
chartMap_sourceChartPoint_eq
loss_sourceChartPoint_eq_centerSq
lossUnit_sourceChartPoint_eq
jacobianPrior_sourceChartPoint_eq_det
loss_monomial_sourceChartPoint
jacobianPrior_monomial_sourceChartPoint
```

Specialize them under:

```text
case1SelectedOldCenterSqFormalJacobianChartCertificate
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate
```

with the same source-point, chart-map, loss, unit, determinant, and monomial
identity names.

## Boundary

- No source production of the hidden selected-old label.
- No proof that the Case 1 chart family covers a neighbourhood.
- No transition regularity theorem.
- No analytic unit-neighbourhood theorem.
- No analytic Jacobian, derivative, or volume-form theorem.
- No total DLN loss monomial identity.
- No global A0 chart family.
- No active-ratio lower bound or chart-count theorem.
- No pole order or RLCT extraction.

## Kill Conditions

- If the `Unit` selected-old token is treated as the source label without the
  selected-old boundary, the statement overclaims.
- If the finite center square-sum is advertised as the total DLN loss, the
  statement overclaims.
- If the formal determinant is advertised as an analytic Jacobian theorem, the
  statement overclaims.
