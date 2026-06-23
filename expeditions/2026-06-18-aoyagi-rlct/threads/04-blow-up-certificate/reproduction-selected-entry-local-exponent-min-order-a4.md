# Reproduction - selected-entry local finite exponent minimum and order

Date: 2026-06-23.

Status: reproduced, formalised, reviewed.

## Source Anchor

Aoyagi PDF p. 6 reads the finite normal-crossing contribution from exponents
`k_j` in the squared loss and `h_j` in the Jacobian/prior factor by the ratio

```text
(h_j + 1) / (2 k_j).
```

The previous selected-entry microcertificate slice proved the local finite
normal-crossing shape for one selected-entry chart.  This slice takes only the
finite exponent consequences of that one-coordinate local certificate.  It
does not identify these numbers with the global A0 exponent minimum or with
the RLCT of the DLN loss.

## Pen-and-Paper Calculation

Let `E` be a finite center, and let `p in E` be the selected pivot.  The
selected-entry microcertificate has one normal-crossing coordinate `u`.
The previous calculation gives

```text
k = 1,
h = |E \ {p}|.
```

Because `p in E`,

```text
|E \ {p}| + 1 = |E|.
```

Therefore the finite ratio at the unique active coordinate is

```text
(h + 1) / (2 k)
  = (|E \ {p}| + 1) / 2
  = |E| / 2.
```

The microcertificate has one chart and one coordinate.  Its unique coordinate
has positive loss exponent, so it is active.  Hence the finite active-ratio
set has only this value, and the local exponent minimum is

```text
|E| / 2.
```

For the order count, every chart has at most one coordinate, while the
finite normal-crossing interface already guarantees that the exponent order is
positive because the minimum is attained by an active coordinate.  Thus the
local finite exponent order of this one-coordinate microcertificate is

```text
1.
```

For the displayed Case 2 residual-block center

```text
E = case2ResidualBlockPivotEntries n S J,
p = (J+1,J+1),
```

the same local finite exponent consequences are

```text
ratio = card(E) / 2,
minimum = card(E) / 2,
order = 1.
```

## Lean Names

```text
selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero
selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two
selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_le_one
selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one
case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero
case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two
case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one
```

## Proved

- The unique coordinate ratio of the generic selected-entry microcertificate
  is `center.card / 2`.
- The generic selected-entry microcertificate's finite exponent minimum is
  `center.card / 2`.
- Every chart in the generic one-chart microcertificate has minimum-coordinate
  count at most `1`.
- The generic selected-entry microcertificate's finite exponent order is `1`.
- The displayed Case 2 specialization has ratio and minimum
  `card(case2ResidualBlockPivotEntries n S J) / 2`.
- The displayed Case 2 specialization has finite exponent order `1`.

## Not Proved

- No global A0 chart family.
- No global active-ratio lower bound for the DLN loss.
- No chart-count theorem for the full A0 data.
- No source production, chart coverage, analytic regularity, analytic
  Jacobian/volume-form theorem, pole order, or RLCT extraction.

## Kill Conditions

- Do not use this local minimum as the global A0 exponent minimum unless the
  full A0 exponent data is identified with this one-coordinate
  microcertificate.
- Do not use the local order `1` as Aoyagi's global pole order.
- Do not treat this finite arithmetic as a replacement for the cited analytic
  normal-crossing-to-RLCT extraction theorem.
