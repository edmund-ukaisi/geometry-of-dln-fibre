# Statement card - A4 Case 1 chart-family boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`5308109873846d1004e8f46924a4aed77051458d`.

Names:

- `DLNFibre.DLN.Aoyagi.case1CenterGenerators_nonempty`
- `DLNFibre.DLN.Aoyagi.case1StripEntries_nonempty_of_bounds`
- `DLNFibre.DLN.Aoyagi.mem_case1CenterGenerators_inr_iff`
- `DLNFibre.DLN.Aoyagi.Case1CenterChartFamilyBoundary`
- `DLNFibre.DLN.Aoyagi.Case1CenterChartFamilyBoundary.chart_regular_of_mem`
- `DLNFibre.DLN.Aoyagi.Case1CenterChartFamilyBoundary.transition_regular_of_mem`
- `DLNFibre.DLN.Aoyagi.Case1CenterChartFamilyBoundary.chart_regular_selectedOld`
- `DLNFibre.DLN.Aoyagi.Case1CenterChartFamilyBoundary.chart_regular_displayedPivot_of_bounds`
- `DLNFibre.DLN.Aoyagi.Case1CenterChartFamilyBoundary.chart_regular_displayedPivot_of_firstJump_colBound`

## Statement

Lean now names the Case 1 selected-entry chart-family assumptions. The finite
Case 1 center is `case1CenterGenerators n S J J1`, with one `Unit` generator
for the already chosen old exceptional variable and right-branch generators
for row-strip entries.

`Case1CenterChartFamilyBoundary` records that every generator in this finite
center satisfies a supplied chart-regularity predicate, and every pair of
generators satisfies a supplied transition-regularity predicate.

Lean also records small finite facts: the Case 1 center is nonempty, the row
strip is nonempty under displayed entry bounds, and right-branch membership is
equivalent to row-strip membership.

## Source Role

This is an assumption boundary. It prevents later Case 1 transition statements
from silently assuming chart coverage, chart regularity, overlap regularity,
or source validity of the hidden old label represented by `Unit`.

Aoyagi displays the old-exceptional-variable chart and the top-left row-strip
pivot chart in Case 1. The non-displayed row-strip selected-entry charts are
finite-center candidates, not source-displayed transition formulas.

## Proved

- The Case 1 finite center is nonempty, witnessed by the old exceptional
  generator.
- Under `1 <= J1` and `J+1 <= n_(S+1)`, the row-strip part is nonempty,
  witnessed by `(J+1,J+1)`.
- A right-branch Case 1 center generator belongs to the center iff its
  underlying pair belongs to the row-strip entry set.
- A supplied boundary package can be projected to chart regularity for any
  member, transition regularity for any two members, old-chart regularity, and
  displayed-pivot regularity under the displayed entry bounds.

## Assumed

- The meanings of `ChartRegular` and `TransitionRegular` are supplied by later
  chart-model work.
- The boundary package assumes those predicates for all finite center members.
- The source validity of the hidden selected old label behind `Unit` remains
  external to this finite-center encoding.

## Not Proved

- No affine blow-up atlas or chart coverage.
- No chart regularity or transition regularity.
- No source validity of the hidden old label represented by `Unit`.
- No source-order transition formula for non-displayed row-strip pivots.
- No chart-produced recurrence or exponent post-data.
- No polynomial-coordinate Jacobian formula or analytic germ-invariance result.
- No source comparability, normal crossings, or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-chart-family-boundary-a4.md`.
- Reproduction check:
  `review-case1-chart-family-boundary-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From the worktree root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory found no Lean forbidden-token use; hits are existing prose
  mentions in expedition notes and statement cards.
