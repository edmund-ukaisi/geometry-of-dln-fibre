# Statement card - A4 selected-entry local ratio chart count

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one`
- `selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one`
- `case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one`
- `case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one`
- `case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one`
- `case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one`

## Claim

For each local selected-entry one-chart finite normal-crossing
microcertificate, the unique chart has exactly one active coordinate at the
local selected-entry ratio.  Equivalently, its chartwise minimum-coordinate
count is `1`.

## Source Role

This is finite bookkeeping on top of the already reproduced selected-entry
microcertificate.  Aoyagi's normal-crossing count on PDF p. 6 counts
coordinates attaining a ratio in a chart.  The local selected-entry
microcertificate has one chart and one active coordinate, and that coordinate
has the local ratio already proved in Lean.

## Inputs Kept Explicit

- the finite center and selected pivot;
- the ordered field assumptions inherited from the local chart certificate;
- for Case 2, the displayed-pivot membership hypotheses `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`;
- for displayed Case 1 row-strip, the finite membership hypotheses `1 <= J1`
  and `J+1 <= n(S+1)`.

## Not Proved

No global A0 chart family, no global active-ratio lower bound, no global
chart-count/order theorem, no selected-entry atlas coverage, no chart
production, no analytic Jacobian/volume-form theorem, no pole order, and no
RLCT extraction.

## Verification

Controller ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused module build, full library build, no-sorry audit, and diff hygiene
check passed through the shared-store workflow.  The full build emitted only
pre-existing Core/style warnings unrelated to this slice.

## Review

Xhigh source/fidelity and Lean/API review passed for the finite-local claim.
See `review-selected-entry-ratio-chart-count-a4.md`.
