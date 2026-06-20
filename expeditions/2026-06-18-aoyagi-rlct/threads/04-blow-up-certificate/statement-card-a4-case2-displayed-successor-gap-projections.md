# Statement card - A4 Case 2 displayed successor gap projections

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.postLevelInvariants`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.successorLeastValueGap`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.postCase2Gap`

## Statement

Lean now exposes, from the displayed top-left Case 2 supplied boundary, the
successor invariant facts already available in the source-selected boundary:
the post-state level/least-value bridge, the successor least-value Case 2 gap,
and the successor recurrence Case 2 gap.

## Source Role

This is a displayed-boundary API projection. It does not add new source
mathematics beyond specializing the existing source-selected supplied boundary
to Aoyagi's displayed pivot `(J+1,J+1)`.

## Proved

- The displayed boundary gives
  `IntroducedLabelLevelInvariants L n S (J+1) post.level leastValue'`.
- The displayed boundary gives
  `case2IntroducedLabelLeastValueGap L n S (J+1) leastValue'`.
- The displayed boundary gives `post.case2Gap`.

## Assumed

- The displayed supplied boundary fields: recurrence post-data, corrected
  exponent post-data, old exponent certificates, old level/least-value bridge,
  old least-value gap, and supplied chart-family predicates.

## Not Proved

- No chart-produced recurrence or exponent post-data.
- No chart coverage, coordinate regularity, Jacobian or volume-form exponent,
  normal crossings, RLCT extraction, termination, transition invariant, or
  printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-displayed-successor-gap-projections-a4.md`.
- Review artifact:
  `review-case2-displayed-successor-gap-projections-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
