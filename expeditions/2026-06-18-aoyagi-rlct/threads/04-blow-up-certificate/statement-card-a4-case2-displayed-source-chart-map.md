# Statement card - A4 Case 2 displayed source-chart map

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceChartMap`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceNormalizedMap`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceChartMap_pivot`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceNormalizedMap_pivot`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceChartMap_of_ne`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceChartMap_eq_mul_normalized`
- `DLNFibre.DLN.Aoyagi.case2Displayed_source_pair_eq_pivot_iff`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceSubstitutionBlock`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceNormalizedBlock`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceSubstitutionBlock_eq_displayedSubstitutionMatrix`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceSubstitutionBlock_eq_mul_normalized`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSource_diagonal_mul_substitutionBlock_pivotFirst`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceNormalizedBlock_mul_sourceFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTransportedFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2DisplayedSourceTransportedFollowingFactor_eq_displayedTransportedFollowingFactor`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceChartMap`

## Statement

Lean now names the source-coordinate displayed top-left Case 2 chart map and
proves that restricting it to the residual row/column block recovers the
existing displayed selected-entry substitution matrix.

The source map sends the selected entry `(J+1,J+1)` to `u` and every other
source residual-block entry to `u` times its residual coordinate. The
normalised source block has pivot value `1`, and the substituted source block
is `u` times the normalised source block.

## Source Role

This follows Aoyagi's displayed Case 2 chart on PDF pp. 19-21. The checkpoint
formalises the elementary source-coordinate substitution and its restriction to
the finite residual block. It also rewrites the displayed supplied boundary's
local `Q/P` identity in the source-chart block names.

## Proved

- Pivot and off-pivot formulas for the displayed source chart map.
- Source-pair equality with `(J+1,J+1)` is equivalent to residual-subtype pair
  equality with the displayed pivot.
- The source normalised/substituted blocks agree with the existing displayed
  block API after source restriction.
- The source substituted block is `u` times the source normalised block.
- The displayed diagonal source-variable transport and following-factor
  transport hold in source-chart names.
- The displayed supplied boundary exports a `Q/P` identity using these
  source-chart block names.

## Assumed

- The continuation bound placing `(J+1,J+1)` in the residual block.
- The supplied displayed boundary hypotheses for the final `Q/P` wrapper:
  recurrence post-data, corrected exponent post-data, and chart-family
  regularity predicates.

## Not Proved

- No chart-produced recurrence or exponent post-data.
- No chart coverage or non-top-left source-displayed chart formula.
- No coordinate regularity, Jacobian computation, normal crossing, RLCT
  extraction, termination, or full transition invariant.
- No repair of the printed Case 2 vector mismatch.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-source-chart-map-a4.md`.
- Review artifact:
  `review-case2-displayed-source-chart-map-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
