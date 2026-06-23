# Statement card - A4 Case 1/Case 2 selected-entry multi-chart specializations

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`
- `lean/DLNFibre/DLN/Aoyagi/Case1FiniteExponentBridge.lean`

Names:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero_eq_selectedCoordinateCount_div_two`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPriorExp_chart_zero_eq_displayedFormalPivotExp`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentMinimum_eq_selectedCoordinateCount_div_two`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_countInChartAtRatio_selectedCoordinateCount_div_two_eq_one`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_minCountInChart_eq_one`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentOrder_eq_one`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.localExponentCoordinateBridge_anyChart`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.localChartFamilyCertificateContribution_summary`
- `case1CenterSqFormalJacobianChartFamilyCertificate`
- `case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero_eq_nonpivotCount_add_one_div_two`
- `case1CenterSqFormalJacobianChartFamilyCertificate.jacobianPriorExp_chart_zero_eq_nonpivotCount`
- `case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two`
- `case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one`
- `case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_minCountInChart_eq_one`
- `case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentOrder_eq_one`
- `case1CenterSqFormalJacobianChartFamilyCertificate.localExponentCoordinateBridge_anyChart`
- `case1CenterSqFormalJacobianChartFamilyCertificate.localChartFamilyCertificateContribution_summary`

## Claim

The generic finite all-pivot selected-entry certificate specializes to the two
Aoyagi finite centers:

```text
case2ResidualBlockPivotEntries n S J
case1CenterGenerators n S J J1
```

For Case 2, under `1 <= S` and
`J+1 <= prefixMinNat n (S+1)`, the all-pivot finite family has ratio and
minimum

```text
((prefixMinNat n S - J) * (n(S+1)-J)) / 2
```

in every pivot chart, chartwise count `1` at that ratio, and finite exponent
order `1`.

For Case 1, the all-pivot finite family has ratio and minimum

```text
(1 + J1 * (n(S+1)-J)) / 2
```

in every pivot chart, chartwise count `1` at that ratio, and finite exponent
order `1`.

The bridge adapters record only the exponent arrays of those finite chart
families.  In Case 2, an arbitrary finite pivot chart has the same erased-center
cardinality as the displayed pivot, so it fits the existing displayed
continuing exponent-coordinate bridge at the level of exponents only.

## Inputs Kept Explicit

- Case 2 continuation assumptions `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`;
- the finite center cardinality lemmas
  `case2ResidualBlockPivotEntries_card`,
  `case1CenterGenerators_card`, and `case1StripEntries_card`;
- ordered-field hypotheses inherited from the selected-entry certificate.

## Not Proved

No source-coordinate formulas for arbitrary non-displayed pivots, no
source-produced `Q/P` transport, no analytic chart coverage, no transition
regularity, no analytic Jacobian or volume-form theorem, no chart-produced
recurrence or exponent post-data, no global A0 active-ratio lower bound, no
global pole order, and no RLCT extraction.

## Verification

Focused checks passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
```

Full verification passed:

```text
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.

## Review

Xhigh independent review passed with no blocking findings.  Durable artifact:
`review-case1-case2-selected-entry-multi-chart-specializations-a4.md`.
