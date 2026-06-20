# Statement card - A4 Case 2 displayed concrete-update boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.displayedPivot_mem`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_displayedPivot`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.transition_regular_selectedPivot_displayedPivot`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_mem`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceSelectedBoundary`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.correctedNewLabel`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.preCase2Gap`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.extendExponentDomain`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.chart_regular_displayedPivot`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_centerIdeal_eq_span_singleton`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceCoordinates`

## Statement

Lean now names the displayed top-left Case 2 supplied boundary and provides a
concrete constructor for the standard recurrence/exponent assignments.

The displayed boundary is the specialization of the source-selected boundary
to the source-displayed pivot `(J+1,J+1)`. The continuation bound supplies this
pivot's residual-block membership. The concrete constructor chooses:

```text
post recurrence state = pre.case2Succ u
corrected exponent post-data = Case2CorrectedExponentPostData.updateSelected
```

and then packages the existing pre-state certificates, level bridge,
least-value gap, and supplied chart-family boundary.

## Source Role

This follows Aoyagi's displayed Case 2 chart on PDF pp. 19-22: the source
writes the top-left pivot chart and then declares successor recurrence data.
Lean names that recurrence assignment together with the expedition's corrected
prefix-minimum exponent assignment as concrete data for the displayed supplied
boundary, while leaving chart production separate.

## Proved

- Displayed pivot membership in the residual-block center from continuation.
- Displayed pivot regularity and selected-to-displayed transition regularity
  from supplied chart-family predicates.
- Source-selected supplied boundary constructor from concrete `case2Succ` and
  corrected `updateSelected` data.
- Displayed supplied boundary wrapper and projection back to the source-selected
  boundary at `(J+1,J+1)`.
- Displayed boundary projections for corrected new label, pre-gap,
  exponent-domain extension, chart regularity, and finite center
  principalization.
- Source-coordinate displayed `Q/P` identity from the displayed supplied
  boundary.

## Assumed

- Pre-state exponent certificates.
- Level/least-value bridge and Case 2 least-value gap.
- Supplied chart-family regularity and transition-regularity predicates.
- Corrected prefix-minimum Case 2 exponent assignment.

## Not Proved

- No chart-produced recurrence or exponent post-data.
- No affine atlas, chart coverage, or coordinate regularity.
- No non-top-left source-displayed Case 2 chart formula.
- No Jacobian, normal crossing, RLCT extraction, termination, source
  comparability, or full transition invariant.
- No repair of the printed Case 2 vector mismatch.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-concrete-update-boundary-a4.md`.
- Review artifact:
  `review-case2-displayed-concrete-update-boundary-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
