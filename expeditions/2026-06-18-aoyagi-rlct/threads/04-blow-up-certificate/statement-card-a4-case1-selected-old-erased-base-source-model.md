# Statement card - A4 Case 1 selected-old erased-base source model

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.levelProductStep_eq_mulStepAt_erase`
- `DLNFibre.DLN.Aoyagi.levelProductStep_erase_eq_of_eq_on_erase`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.erasedStep`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.step_eq_mulStepAt_erasedStep`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.post_erasedStep_eq_pre_erasedStep`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.pre_step_eq_mulStepAt`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.post_step_eq_mulStepAt`
- `DLNFibre.DLN.Aoyagi.Case1SelectedOldLoweredRecurrenceBoundary.of_levelMoveData`

## Statement

Lean now derives the Case 1(1) lowered-boundary recurrence equalities from a
finite-product source model.  The base recurrence is the introduced-label
recurrence with the selected old label `(s0,k0)` erased.  If the pre-state
reinserts that selected variable at level `J+J1`, the post-state reinserts the
same variable at level `J`, and all non-selected introduced-label data agree,
then:

```text
pre.step  = mulStepAt(pre.erasedStep s0 k0,u,J+J1),
post.step = mulStepAt(pre.erasedStep s0 k0,u,J).
```

The constructor `Case1SelectedOldLoweredRecurrenceBoundary.of_levelMoveData`
instantiates the existing lowered-recurrence boundary with this erased base
recurrence.

## Source Role

This matches Aoyagi Case 1(1), PDF pp. 15-16: the selected old variable has
level `J+J1` before the selected-old chart and level `J` after the level
lowering, while the branch stays on the same `(S,J)` introduced-label domain.

## Proved

- Finite-product erase/reinsert gives a `mulStepAt` recurrence at the selected
  label's level.
- Agreement away from the erased selected label preserves the erased base
  recurrence.
- The Case 1(1) moved-level data derives both pre/post step equalities.
- The existing lowered-recurrence boundary can be built with
  `baseStep = pre.erasedStep s0 k0`.

## Not Proved

- No construction of the selected-old chart from raw coordinates.
- No derivation of selected-label facts from the `Unit` center token.
- No domain advancement to `(S,J+1)`.
- No Case 1(2) displayed pivot, `Q/P`, chart coverage, chart regularity,
  Jacobian, normal crossings, RLCT extraction, or full transition invariant.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-erased-base-source-model-a4.md`.
- Review artifact:
  `review-case1-selected-old-erased-base-source-model-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
