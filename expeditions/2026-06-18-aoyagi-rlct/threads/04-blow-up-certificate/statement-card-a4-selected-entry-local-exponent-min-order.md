# Statement card - A4 selected-entry local finite exponent minimum and order

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`
- `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`
- `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_le_one`
- `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`

## Claim

For the selected-entry one-coordinate finite normal-crossing microcertificate,
the unique coordinate has finite ratio `center.card / 2`, the local finite
exponent minimum is `center.card / 2`, and the local finite exponent order is
`1`.  The displayed Case 2 residual-block specialization gives the same
statements with `center = case2ResidualBlockPivotEntries n S J`.

## Inputs Kept Explicit

- the finite selected-entry center and pivot;
- the ordered field assumptions needed by the underlying chart certificate;
- for Case 2, `1 <= S` and `J+1 <= prefixMinNat n (S+1)`, which put the
  displayed pivot `(J+1,J+1)` in the residual-block center.

## Proved

The generic selected-entry microcertificate has finite data with one chart and
one coordinate.  At its unique coordinate,

```text
k = 1,
h = card(center.erase pivot),
h + 1 = center.card,
```

so the finite ratio is `center.card / 2`.  Since there is only one active
coordinate, the finite exponent minimum is the same.  Every chart has at most
one minimum coordinate and the finite exponent interface gives positivity of
the order, so the local exponent order is `1`.

## Not Proved

No global A0 chart family, no global DLN active-ratio lower bound, no global
chart-count/order theorem, no source production, no chart coverage, no
analytic regularity, no analytic Jacobian/volume-form theorem, no pole order,
and no RLCT extraction.

## Verification

Controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

The focused file check, focused Lake target, full aggregator build, no-sorry
check, and diff hygiene check passed.  The full aggregator build emitted only
unrelated pre-existing Core linter warnings.

## Review

Xhigh fidelity/bedrock review passed.  See
`review-selected-entry-local-exponent-min-order-a4.md`.
