# Statement card - A4 Case 2 chart-family boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`pending-checkpoint`.

Names:

- `DLNFibre.DLN.Aoyagi.SelectedEntryChartFamilyBoundary`
- `DLNFibre.DLN.Aoyagi.Case2ResidualBlockChartFamilyBoundary`
- `DLNFibre.DLN.Aoyagi.case2ResidualBlockPivotEntries_nonempty_of_cont`
- `DLNFibre.DLN.Aoyagi.Case2ResidualBlockChartFamilyBoundary.chart_regular_of_mem`
- `DLNFibre.DLN.Aoyagi.Case2ResidualBlockChartFamilyBoundary.transition_regular_of_mem`
- `DLNFibre.DLN.Aoyagi.Case2ResidualBlockChartFamilyBoundary.chart_regular_displayedPivot_of_cont`

## Statement

Lean now names the remaining selected-entry chart-family assumptions. A generic
`SelectedEntryChartFamilyBoundary` records that every selected entry in a
finite center satisfies a supplied chart-regularity predicate, and every pair
of selected entries satisfies a supplied transition-regularity predicate.

The Case 2 specialization applies this to
`case2ResidualBlockPivotEntries n S J`. Under the continuation hypothesis, the
finite residual-block pivot set is nonempty because it contains the displayed
top-left pivot `(J+1,J+1)`.

## Source Role

This is an assumption boundary. It prevents later transition statements from
silently assuming chart coverage, chart regularity, or overlap regularity. It
does not prove those properties.

## Proved

- The displayed Case 2 pivot belongs to the residual-block center under the
  existing continuation hypothesis, so that finite pivot set is nonempty.
- A supplied boundary package can be projected to chart regularity for any
  member, transition regularity for any two members, and displayed-pivot
  regularity under continuation.

## Assumed

- The meanings of `ChartRegular` and `TransitionRegular` are supplied by later
  chart-model work.
- The boundary package assumes those predicates for all finite center members.

## Not Proved

- No affine blow-up atlas or chart coverage.
- No chart regularity or transition regularity.
- No source-order transition formula for non-displayed pivots.
- No chart-produced recurrence or exponent post-data.
- No polynomial-coordinate Jacobian formula or analytic germ-invariance result.
- No source comparability, normal crossings, or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-chart-family-boundary-a4.md`.
- Reproduction check:
  `review-case2-chart-family-boundary-a4.md`.

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
