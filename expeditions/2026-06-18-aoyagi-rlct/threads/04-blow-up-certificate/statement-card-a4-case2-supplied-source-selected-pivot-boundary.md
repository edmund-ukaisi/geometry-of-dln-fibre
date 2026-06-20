# Statement card - A4 Case 2 supplied source-selected pivot boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.correctedNewLabel`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.preCase2Gap`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.extendExponentDomain`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.postLevelInvariants`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.successorLeastValueGap`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.postCase2Gap`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_selectedPivot`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_of_mem`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.transition_regular_selectedPivot_of_mem`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.selectedPivot_centerIdeal_eq_span_singleton`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP`

## Statement

Lean now packages a supplied boundary for a Case 2 source-selected residual
block pivot. A supplied source pair

```text
p in case2ResidualBlockPivotEntries n S J
```

is combined with:

- source continuation bounds;
- pre-state exponent certificates;
- the level/least-value bridge and Case 2 least-value gap;
- supplied recurrence post-data;
- supplied corrected exponent post-data;
- supplied finite chart-family regularity predicates.

The package derives the corrected new-label certificate, old and successor
Case 2 gaps, the successor exponent-domain certificate, selected-pivot
chart-family projections, finite center principalization, and the existing
source-selected arbitrary-pivot `Q/P` identity.

## Source Role

This checkpoint is a glue boundary. It makes the already proved arbitrary
selected-pivot finite algebra usable from source-coordinate residual and
following-factor functions, while keeping all chart-family and post-data
production assumptions explicit.

## Proved

- Corrected new-label certificate from source continuation bounds.
- Pre-state recurrence gap from integer least-value gap plus
  `leastValue = level`.
- Successor exponent-domain certificate from corrected exponent post-data.
- Successor level/least-value bridge and Case 2 gaps.
- Supplied chart regularity and transition regularity projections.
- Selected-entry principalization of the finite residual-block center to
  `(u)`.
- Source-selected arbitrary-pivot `Q/P` identity with successor recurrence
  weights.

## Assumed

- A supplied pivot membership proof in `case2ResidualBlockPivotEntries n S J`.
- Supplied `ChartRegular` and `TransitionRegular` predicates.
- Supplied recurrence post-data and corrected exponent post-data.
- The corrected prefix-minimum Case 2 certificate, not the PDF's printed
  actual-width vector outside the known compatibility cases.

## Not Proved

- No affine blow-up atlas or chart coverage.
- No source-displayed non-top-left Case 2 chart formula.
- No chart-produced recurrence or exponent post-data.
- No regularity or transition regularity from coordinates.
- No Jacobian, normal crossing, RLCT extraction, termination, or full
  transition invariant.
- No repair of the printed Case 2 vector mismatch.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-supplied-source-selected-pivot-boundary-a4.md`.
- Review artifact:
  `review-case2-supplied-source-selected-pivot-boundary-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
