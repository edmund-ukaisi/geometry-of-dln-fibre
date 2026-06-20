# Statement card - A4 Case 2 source-selected chart-map adapter

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.case2SourceSelectedChartMapOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedNormalizedMapOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedChartMapOfMem_pivot`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedNormalizedMapOfMem_pivot`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedChartMapOfMem_of_ne`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedChartMapOfMem_eq_mul_normalized`
- `DLNFibre.DLN.Aoyagi.case2SourceSelected_source_pair_eq_pivot_iff`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedSubstitutionBlockOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedNormalizedBlockOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedNormalizedBlockOfMem_eq_selectedNormalizedMatrixOfMem`
- `DLNFibre.DLN.Aoyagi.case2SourceSelectedSubstitutionBlockOfMem_eq_selectedSubstitutionMatrixOfMem`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP_sourceChartMap`

## Statement

Lean now names the source-coordinate selected-entry chart map for any supplied
Case 2 residual-block pivot `p`.  The map is total on source coordinate pairs,
but all source-faithful statements restrict it to the finite residual block via
`hp : p in case2ResidualBlockPivotEntries n S J`.

The restricted source-coordinate substituted and normalized blocks are proved
equal to the existing subtype-indexed selected-pivot matrices.  The supplied
source-selected boundary then exports its `Q/P` identity in these source-chart
map names.

## Source Role

Aoyagi displays the top-left Case 2 chart on PDF pp. 19-21.  This checkpoint
does not add a displayed non-top-left source formula.  It abstracts the same
selected-entry finite algebra for a supplied residual-block pivot so that the
existing arbitrary-pivot supplied boundary can be stated in source-coordinate
chart-map names.

## Proved

- Source selected-entry chart and normalized maps for a supplied Case 2 pivot.
- Pivot and off-pivot source-coordinate values.
- Pointwise factorization by the selected variable.
- Source-pair equality iff residual subtype pivot equality.
- Restricted source-coordinate substituted and normalized blocks agree with
  the existing source-selected matrices.
- The supplied source-selected `Q/P` theorem in source-chart-map notation.

## Assumed

- The pivot membership proof `p in case2ResidualBlockPivotEntries n S J`.
- For the boundary theorem: the existing supplied source-selected chart-family
  boundary, including recurrence post-data, corrected exponent post-data, old
  gap, and regularity predicates.

## Not Proved

- No chart coverage or atlas construction.
- No claim that Aoyagi displays non-top-left source charts.
- No chart-produced recurrence or exponent post-data.
- No coordinate regularity, Jacobian/volume calculation, normal crossings,
  RLCT extraction, termination, transition invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-source-selected-chart-map-a4.md`.
- Review artifact:
  `review-case2-source-selected-chart-map-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
