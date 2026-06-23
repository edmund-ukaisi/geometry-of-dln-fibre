# Statement card - A4 Case 1 selected-entry chart-family data

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `Case1CenterSelectedEntryChartFamilyData`
- `Case1CenterSelectedEntryChartFamilyData.standard`
- `Case1CenterSelectedEntryChartFamilyData.selectedOldPivot`
- `Case1CenterSelectedEntryChartFamilyData.displayedPivot`
- `Case1CenterSelectedEntryChartFamilyData.selectedOldPivot_val`
- `Case1CenterSelectedEntryChartFamilyData.displayedPivot_val`
- `Case1CenterSelectedEntryChartFamilyData.standard_value_selectedOldPivot`
- `Case1CenterSelectedEntryChartFamilyData.standard_value_displayedPivot`
- `Case1CenterSelectedEntryChartFamilyData.standard_selectedOld_selected_mem_valueSet`
- `Case1CenterSelectedEntryChartFamilyData.standard_displayedPivot_selected_mem_valueSet`
- `Case1CenterSelectedEntryChartFamilyData.standard_centerSq_selectedOldPivot`
- `Case1CenterSelectedEntryChartFamilyData.standard_centerSq_displayedPivot`
- `Case1CenterSelectedEntryChartFamilyData.standard_centerIdeal_selectedOldPivot_eq_span_singleton`
- `Case1CenterSelectedEntryChartFamilyData.standard_centerIdeal_displayedPivot_eq_span_singleton`

## Statement

Lean now specializes the generic finite selected-entry chart-family data to the
Case 1 center.  The old exceptional generator is represented by a left `Unit`
token, and row-strip entries are represented by right-branch pairs.

For the selected-old and displayed top-left row-strip pivots, Lean proves the
definitional selected-entry value formulas and the immediate finite algebra
consequences:

```text
selected variable occurs in the transformed center values,
center square-sum = u^2 * (1 + erased-center square-sum),
Ideal(transformed center values) = (u).
```

## Source Role

Aoyagi PDF pp. 16-17 display exactly the old-variable chart and the top-left
row-strip chart.  The standard family also has finite coordinates for every
Case 1 center member, but non-displayed row-strip pivots are only finite
chart candidates here, not source-produced transition formulas.

## Inputs Kept Explicit

- The finite Case 1 center `case1CenterGenerators n S J J1`.
- For the displayed row-strip pivot, the finite bounds `1 <= J1` and
  `J+1 <= n(S+1)`.
- A semiring or commutative semiring coefficient type, depending on the
  finite algebra statement.

## Not Proved

No source validity of the hidden old label represented by `Unit`, no
source-displayed transition formula for arbitrary row-strip pivots, no chart
coverage, no chart regularity or transition regularity, no chart-produced
recurrence or exponent post-data, no analytic Jacobian or volume-form theorem,
no normal crossings, no pole order, and no RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-entry-chart-family-data-a4.md`.
- Review artifact:
  `review-case1-selected-entry-chart-family-data-a4.md`.

## Verification

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
```
