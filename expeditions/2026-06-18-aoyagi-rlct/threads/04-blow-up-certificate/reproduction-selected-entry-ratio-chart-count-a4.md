# Reproduction - selected-entry local ratio chart count

Date: 2026-06-23.

Status: reproduced, formalised, reviewed.

## Source Anchor

Aoyagi PDF p. 6 reads the finite normal-crossing order from the number of
coordinates in a chart that attain the minimum ratio

```text
(h_j + 1) / (2 k_j).
```

The previous selected-entry microcertificate and local-exponent slices already
reproduced the finite selected-entry chart, the square-sum factorisation, the
formal pivot-first determinant exponent, and the local one-coordinate ratio.
This slice adds only the ratio-specific chart count for that same local
microcertificate.  It does not claim a global A0 chart family or the pole
order of the DLN loss.

## Pen-and-Paper Calculation

Let `E` be a finite center and let `p in E` be the selected pivot.  The local
selected-entry microcertificate has one chart and one coordinate `u`.  The
previous calculation gives

```text
k = 1,
h = |E \ {p}|,
(h + 1) / (2 k) = |E| / 2.
```

The A0 finite interface counts, in each chart, coordinates whose loss exponent
is positive and whose ratio equals a specified candidate ratio.  For the local
selected-entry microcertificate, the only chart has the one coordinate `u`.
At `u`,

```text
k = 1 > 0,
ratio(u) = |E| / 2.
```

Therefore the chartwise set at the local ratio is exactly `{u}`, and its
cardinality is

```text
1.
```

Since the local finite exponent minimum is also `|E| / 2`, the chartwise
minimum-coordinate count is the same count:

```text
minCountInChart = 1.
```

For Aoyagi's displayed Case 2 residual-block center

```text
E = case2ResidualBlockPivotEntries n S J,
p = (J+1,J+1),
```

the local ratio-specific chart count is

```text
countInChartAtRatio(card(E)/2) = 1.
```

For the two displayed Case 1 selected-entry microcertificates, the erased
center has cardinality

```text
J1 * (M^(S+1)-J),
```

so the full center has cardinality

```text
1 + J1 * (M^(S+1)-J).
```

Thus the ratio-specific chart count at

```text
(1 + J1 * (M^(S+1)-J)) / 2
```

is again `1` for both the selected-old chart and the displayed row-strip
chart.

## Lean Targets

```text
selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one
selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one

case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one
case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one

case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one
case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one

case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one
case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one
```

## Lean Status

The targets above are proved in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`.

## Proved By This Slice

- In the generic selected-entry one-chart microcertificate, the chart count at
  the local ratio `center.card / 2` is `1`.
- The corresponding chartwise minimum-coordinate count is `1`.
- The displayed Case 2 and displayed Case 1 local microcertificates inherit
  these exact ratio-count facts with their source-facing ratio formulas.

## Not Proved

- No global A0 active-ratio lower bound.
- No global A0 chart-count/order theorem.
- No chart coverage or selected-entry atlas.
- No source production of successor charts or suffixes.
- No analytic Jacobian, derivative, volume-form, or transition-regularity
  theorem.
- No pole order or RLCT extraction.

## Kill Conditions

- Do not use this local count as the global pole order of Aoyagi Theorem 2.
- Do not apply the count to any exponent data other than the local
  selected-entry one-chart microcertificate unless a separate theorem embeds
  that microcertificate into genuine global A0 data.
- Do not infer all-chart upper bounds for the full DLN normal-crossing family
  from this one-chart local count.
