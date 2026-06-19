# Statement card - A4 Case 1 selected-old source substitution

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`0c958d624d5f89c6fc5766a32bae6bc29fe9e61a`.

Names:

- `DLNFibre.DLN.Aoyagi.levelProductStep_updateVar_eq_mul_of_mem`
- `DLNFibre.DLN.Aoyagi.levelProductStep_updateVar_eq_of_ne`
- `DLNFibre.DLN.Aoyagi.levelProductStep_eq_mulStepAt_of_updateSelected`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_selectedLevel_eq_mul`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_of_ne_selectedLevel`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_mulStepAt_selectedLevel`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_mulStepAt_of_firstJump`
- `DLNFibre.DLN.Aoyagi.case1ResidualRowStripOldWeight_eq_sourceWeight_of_selectedOldFactoredBase`

## Statement

Lean now proves the same-domain recurrence substitution for the hidden old
selected variable in Case 1(2).

If `source` is the pulled-back source recurrence after `old = u * old'`, and
`factoredBase` is the recurrence using the residual old variable `old'`, then
the supplied factorisation data imply

```text
source.step = mulStepAt factoredBase.step u (J+J1).
```

The row-strip corollary rewrites `case1RowStripOldWeight` as the substituted
source recurrence weights on residual rows.

## Source Role

This is the elementary recurrence interface behind Aoyagi's Case 1(2)
selected-old chart on PDF p. 17. It explains why the old selected factor at
level `J+J1` affects source weights only below the displayed row strip.

## Proved

- Scaling one existing finite-product variable scales exactly the recurrence
  factor at that variable's level.
- All other recurrence factors are unchanged.
- Under supplied Case 1 selected-old factored-base data, the substituted
  source recurrence is `mulStepAt factoredBase.step u (J+J1)`.
- The row-strip old-weight convention equals substituted source recurrence
  weights on residual rows.

## Assumed

- The selected old label is introduced.
- The substituted source and factored-base states have the same levels.
- The selected source variable is `u * factoredBase.var s0 k0`.
- All other introduced variables agree.
- First-jump data supplies the selected level `J+J1`.

## Not Proved

- No construction of the selected-old chart.
- No theorem connecting the `Unit` center generator to the hidden old label.
- No construction of the factored-base state.
- No chart-produced recurrence or exponent post-data.
- No chart coverage, regularity, transition regularity, or Jacobian formula.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-selected-old-source-substitution-a4.md`.
- Review artifact:
  `review-case1-selected-old-source-substitution-a4.md`.

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
