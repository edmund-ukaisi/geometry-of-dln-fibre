# Statement card - A4 Case 1 selected-old supplied chart-family boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`a20e0f4ef4fc2d539fa9f8e220e985cf8744a648`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourcePullback_selectedIntroduced`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.selectedLevel`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.selectedOld_mem_center`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_mem_center`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.chart_regular_selectedOld`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.chart_regular_displayedPivot`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.transition_regular_selectedOld_displayedPivot`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.transition_regular_displayedPivot_selectedOld`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.source_step_eq_mulStepAt`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.extendExponentDomain`

## Statement

Lean now packages a supplied chart-family boundary for the displayed Case 1(2)
selected-old pullback. It combines the selected-old pullback/local handoff
boundary with a supplied `Case1CenterChartFamilyBoundary`.

The package projects chart regularity and transition regularity for the
selected old token and displayed top-left row-strip pivot, and it reuses the
selected-old source step, source-order identity, and exponent-domain extension.

## Source Role

This matches the source boundary around Aoyagi PDF pp. 15-19: the old label
`u_(s,k)` is chosen by first-jump data, the Case 1 center includes that old
generator and the row strip, and the displayed Case 1(2) chart uses the
top-left row-strip pivot. The package records supplied regularity data for
these finite center choices without constructing the charts.

## Proved

- The selected old token and displayed top-left row-strip pivot are finite
  center members under the bundled hypotheses.
- Supplied chart regularity and transition regularity apply to those two
  center members.
- Selected-label, source-step, source-order, and exponent-domain projections
  remain available through the combined boundary.

## Assumed

- Supplied selected-old pullback/local handoff data.
- Supplied Case 1 finite chart-family regularity and transition regularity.
- Supplied factored-base and post recurrence states.
- Supplied exponent pre/post data and normalized pivot block for the
  source-order projection.

## Not Proved

- No construction of a blow-up chart or affine atlas.
- No proof that the `Unit` center token itself determines `(s0,k0)`.
- No construction of the raw-coordinate-to-`source` pullback.
- No proof of chart coverage, regularity, transition regularity, or Jacobian
  formula from coordinates.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-supplied-chart-family-boundary-a4.md`.
- Review artifact:
  `review-case1-selected-old-supplied-chart-family-boundary-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- `git diff --check`
- `rg -n "(^|[^A-Za-z0-9_])(sorry|axiom|native_decide|#exit)([^A-Za-z0-9_]|$)" lean/DLNFibre/DLN/Aoyagi`
