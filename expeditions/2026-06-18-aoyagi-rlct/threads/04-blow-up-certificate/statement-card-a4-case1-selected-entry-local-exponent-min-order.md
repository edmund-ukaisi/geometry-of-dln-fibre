# Statement card - A4 Case 1 selected-entry local exponent minimum and order

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case1SelectedOldCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`
- `case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`
- `case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two`
- `case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`

## Statement

For the two displayed Case 1 selected-entry finite microcertificates, Lean
proves that the local finite exponent ratio and local finite exponent minimum
are

```text
(1 + J1 * (n(S+1)-J)) / 2,
```

and that the local finite exponent order is `1`.

## Source Role

This composes two already reproduced finite calculations:

- Case 1 erasing either displayed pivot leaves
  `J1 * (n(S+1)-J)` non-pivot center generators.
- The generic selected-entry one-chart microcertificate has loss exponent
  `1`, ratio `center.card/2`, local finite minimum `center.card/2`, and local
  finite order `1`.

The result is the local one-coordinate finite exponent contribution for
Aoyagi's Case 1(1) and Case 1(2) selected charts on PDF pp. 16-17.

## Inputs Kept Explicit

- For the old selected generator, only `n`, `S`, `J`, and `J1`.
- For the displayed row-strip pivot, the finite membership hypotheses
  `1 <= J1` and `J+1 <= n(S+1)`.
- An ordered field coefficient type, inherited from the generic
  selected-entry microcertificate.

## Not Proved

No analytic Jacobian or volume-form theorem, no chart coverage, no transition
regularity, no source construction of the hidden old selected label, no
chart-produced recurrence or exponent post-data, no global A0 active-ratio
lower bound or exponent minimum, no global chart-count/order theorem, no pole
order, and no RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-entry-local-exponent-min-order-a4.md`.
- Review artifact:
  `review-case1-selected-entry-local-exponent-min-order-a4.md`.

## Verification

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```
