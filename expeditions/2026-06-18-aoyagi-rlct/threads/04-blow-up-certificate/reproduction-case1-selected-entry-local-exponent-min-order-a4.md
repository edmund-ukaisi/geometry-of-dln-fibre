# Reproduction - Case 1 selected-entry local exponent minimum and order

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

## Source Anchor

Aoyagi PDF p. 6 reads finite normal-crossing exponents from a display with
loss exponents `k_j` and Jacobian/prior exponents `h_j`, using the ratio

```text
(h_j + 1) / (2 k_j).
```

Aoyagi PDF pp. 16-17 display the two Case 1 selected charts:

- Case 1(1), where the old exceptional variable is selected;
- Case 1(2), where the top-left row-strip variable `d_(J+1,J+1)` is selected.

The previous Case 1 cardinality slice proved the finite formal determinant
exponent for both charts.  The previous selected-entry local-exponent slice
proved the generic one-chart finite exponent arithmetic.  This note composes
only those two finite facts.

## Pen-And-Paper Calculation

Let

```text
h = J1 * (M^(S+1) - J).
```

In Case 1, the blow-up center has one old exceptional generator and the row
strip

```text
J+1 <= i <= J+J1,
J+1 <= j <= M^(S+1).
```

The row strip has cardinality `h`, so the finite center has cardinality

```text
1 + h.
```

In the selected-entry chart, if the pivot coordinate is `u`, then the finite
center square-sum pulls back as

```text
sum x_e^2 = u^2 * (1 + sum y_e^2).
```

Thus the loss exponent is

```text
k = 1.
```

For both displayed Case 1 pivots, erasing the pivot leaves exactly `h`
non-pivot center generators:

- selecting the old exceptional generator leaves all `h` row-strip entries;
- selecting `d_(J+1,J+1)` leaves the old exceptional generator and the other
  `h-1` row-strip entries.

The formal pivot-first determinant exponent is therefore

```text
h = J1 * (M^(S+1) - J).
```

The local finite ratio at the unique coordinate is

```text
(h + 1) / (2 * 1)
  = (1 + J1 * (M^(S+1) - J)) / 2.
```

Since the microcertificate has one chart and one active coordinate, its local
finite exponent minimum is the same ratio, and its local finite exponent order
is

```text
1.
```

## Lean Names

```text
case1SelectedOldCenterSqFormalJacobianChartCertificate.lossExp_zero_zero
case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero
case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two
case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one

case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.lossExp_zero_zero
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one
```

The displayed row-strip theorems keep the finite membership hypotheses
`1 <= J1` and `J+1 <= n(S+1)` explicit.

## Proved

- The unique local coordinate in each displayed Case 1 finite
  microcertificate has loss exponent `1`.
- The unique local coordinate ratio is
  `(1 + J1 * (n(S+1)-J)) / 2`.
- The local finite exponent minimum is
  `(1 + J1 * (n(S+1)-J)) / 2`.
- The local finite exponent order is `1`.

## Not Proved

- No analytic Jacobian, derivative, or volume-form theorem.
- No chart coverage or transition regularity.
- No source construction of the hidden old selected label.
- No chart-produced recurrence or exponent post-data.
- No global A0 active-ratio lower bound or global A0 exponent minimum.
- No global chart-count/order theorem, pole order, or RLCT extraction.

## Kill Conditions

- Do not use the erased-center count `J1 * (n(S+1)-J)` as the ratio numerator;
  the local ratio numerator is `1 + J1 * (n(S+1)-J)`.
- Do not use the local order `1` as Aoyagi's global pole order.
- Do not treat this local one-chart certificate as the global A0
  normal-crossing chart family for the DLN loss.
