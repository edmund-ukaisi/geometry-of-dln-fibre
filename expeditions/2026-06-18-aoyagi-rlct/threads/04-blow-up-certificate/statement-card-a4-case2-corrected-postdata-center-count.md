# Statement card - A4 Case 2 corrected post-data center count

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case2CorrectedExponentPostData.numerator_new_eq_correctedNumerator`
- `DLNFibre.DLN.Aoyagi.Case2CorrectedExponentPostData.numerator_new_eq_card_of_cont`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.numerator_new_eq_correctedNumerator`
- `DLNFibre.DLN.Aoyagi.Case2SourceSelectedSuppliedChartFamilyBoundary.numerator_new_eq_card`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.numerator_new_eq_correctedNumerator`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.numerator_new_eq_card`

## Statement

Lean now projects the supplied corrected Case 2 exponent post-data to the
finite selected-coordinate count. The corrected post-data assigns the new label
`(S,J+1)` the named numerator `correctedCase2NewLabelNumerator n S J`; under
displayed continuation this equals the integer cardinality of
`case2ResidualBlockPivotEntries n S J`.

The same projection is exported from the source-selected and displayed supplied
Case 2 boundary packages.

## Source Role

This follows the displayed Case 2 scalar update on Aoyagi PDF pp. 19-21 after
the center-count reproduction. It records that the corrected numerator field is
the selected residual-block coordinate count.

## Proved

- Supplied corrected post-data assigns the new label the corrected numerator.
- Under displayed continuation, that numerator equals the selected
  residual-block coordinate count.
- Source-selected and displayed supplied boundary packages expose the same
  projection.

## Assumed

- The corrected Case 2 exponent post-data is supplied.
- For the cardinality projection: displayed continuation
  `J+1 <= prefixMinNat n (S+1)` and `1 <= S`.

## Not Proved

- No chart-produced exponent post-data.
- No Jacobian exponent or volume-form calculation.
- No chart coverage, coordinate regularity, normal crossing, RLCT extraction,
  termination, or transition invariant.
- No repair of the printed Case 2 vector mismatch.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-corrected-postdata-center-count-a4.md`.
- Review artifact:
  `review-case2-corrected-postdata-center-count-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
