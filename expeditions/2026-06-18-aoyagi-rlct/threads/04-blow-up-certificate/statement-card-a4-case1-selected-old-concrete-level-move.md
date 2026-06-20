# Statement card - A4 Case 1 selected-old concrete level move

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldLevelMove`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_level_selected`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_level_of_ne`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_var`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_levelMoveData`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary.of_sameDomain_case1SelectedOldLevelMove`

## Statement

Lean now defines the concrete same-domain recurrence post-state for Aoyagi
Case 1(1):

```text
pre.case1SelectedOldLevelMove s0 k0.
```

It changes only the selected old label's recurrence level to the current pivot
level `J`, leaves every recurrence-label variable unchanged, and leaves every
non-selected level unchanged.

If the selected old label is introduced and `pre.level s0 k0 = J+J1`, then the
concrete state supplies `Case1SelectedOldLevelMoveData` with selected scalar
`pre.var s0 k0`.  The constructor
`Case1SelectedOldLoweredRecurrenceBoundary.of_sameDomain_case1SelectedOldLevelMove`
then instantiates the erased-base lowered boundary directly from a
`sameDomain` package stated over `pre.level`.

## Source Role

This matches Aoyagi Case 1(1), PDF pp. 15-16: the branch stays at `(S,J)`,
keeps the selected old variable as the selected chart denominator, and lowers
the selected old level from `J+J1` to `J`.

## Proved

- The concrete post-state has selected level `J`.
- Non-selected levels and all recurrence-label variables are unchanged.
- The concrete post-state supplies the existing moved-level recurrence data.
- The existing lowered-recurrence boundary can be instantiated with this
  concrete post-state and `baseStep = pre.erasedStep s0 k0`.

## Not Proved

- No construction of the selected-old chart from raw coordinates.
- No proof that raw source coordinates produce this recurrence post-state.
- No inference of `(s0,k0)` from the `Unit` finite-center token.
- No domain advancement to `(S,J+1)`.
- No Case 1(2) displayed pivot, `Q/P`, chart coverage, chart regularity,
  Jacobian, normal crossings, RLCT extraction, or full transition invariant.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-concrete-level-move-a4.md`.
- Review artifact:
  `review-case1-selected-old-concrete-level-move-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
