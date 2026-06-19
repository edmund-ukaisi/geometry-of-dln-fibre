# Statement card - A4 Case 1 selected-old pullback boundary

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`d4e754f701dabb615a3b8f2e9566aba2e319ae4e`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.factoredBaseFirstJump`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.selectedOld_mem_center`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.sourcePullback_selectedIntroduced`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.selectedLevel`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.source_step_eq_mulStepAt`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.residualRowStripOldWeight_eq_sourceWeight`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.sourceOrder_identity`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.extendExponentDomain`

## Statement

Lean now packages the supplied Case 1(2) selected-old pullback boundary:
selected-old source recurrence data plus the displayed row-strip local handoff
specialized to `factoredBase.level`.

The package exposes the source-facing consequences needed downstream:
source recurrence substitution, old-center membership for the `Unit` token,
row-strip old-weight rewriting into `source.weight`, the source-order identity,
and exponent-domain extension.

## Source Role

This follows Aoyagi PDF pp. 16-17: the Case 1 center has an old exceptional
generator and row-strip entries, and Case 1(2) rewrites the old variable as
`old = u * old'`. The package records this source-facing boundary without
claiming that Lean has constructed the chart.

## Proved

- A supplied selected-old pullback and supplied displayed local handoff can be
  bundled without an extra `level = factoredBase.level` argument.
- The selected-old source step is `mulStepAt factoredBase.step u (J+J1)`.
- The row-strip old-weight convention rewrites to supplied source weights.
- The displayed source-order identity and exponent-domain extension follow
  from the bundled data.

## Assumed

- Supplied selected-old pullback recurrence data.
- Supplied displayed row-strip local handoff data.
- Supplied factored-base and post recurrence states.
- Supplied exponent pre/post data and normalized pivot block for the
  source-order projection.

## Not Proved

- No construction of the selected-old chart.
- No proof that the `Unit` center token itself determines the source label
  `(s0,k0)`.
- No construction of the raw-coordinate-to-`source` pullback.
- No chart coverage, chart regularity, transition regularity, or Jacobian
  formula.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-pullback-boundary-a4.md`.
- Review artifact:
  `review-case1-selected-old-pullback-boundary-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
  passed.
- From `lean/`: `lake build DLNFibre` passed.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From repository root: `git diff --check` passed.
- Xhigh review passed after one documentation correction.
