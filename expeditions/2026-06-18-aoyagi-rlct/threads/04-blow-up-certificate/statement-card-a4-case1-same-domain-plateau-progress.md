# Statement card - A4 Case 1(1) same-domain plateau progress

Date: 2026-06-30.

## Statement

Add a finite same-domain progress kernel for Aoyagi Case 1(1), based on
recurrence levels over the already introduced labels at `(S,J)`.

Lean names:

```text
IntroducedLabelRecurrenceState.levelPlateau
IntroducedLabelRecurrenceState.mem_levelPlateau
IntroducedLabelRecurrenceState.levelPlateauProgress
IntroducedLabelRecurrenceState.levelPlateauProgress_wellFounded
IntroducedLabelRecurrenceState.abovePivotLevelFinset
IntroducedLabelRecurrenceState.mem_abovePivotLevelFinset
IntroducedLabelRecurrenceState.abovePivotLevelProgress
IntroducedLabelRecurrenceState.abovePivotLevelProgress_wellFounded
IntroducedLabelRecurrenceState.levelPlateau_eq_erase_of_case1SelectedOldLevelMoveData
IntroducedLabelRecurrenceState.levelPlateauProgress_of_case1SelectedOldLevelMoveData
IntroducedLabelRecurrenceState.levelPlateauProgress_case1SelectedOldLevelMove_of_sameDomain
IntroducedLabelRecurrenceState.abovePivotLevelFinset_eq_erase_of_case1SelectedOldLevelMoveData
IntroducedLabelRecurrenceState.abovePivotLevelProgress_of_case1SelectedOldLevelMoveData
IntroducedLabelRecurrenceState.abovePivotLevelProgress_case1SelectedOldLevelMove_of_sameDomain
```

The exact plateau theorem proves that a supplied Case 1(1) selected-old level
move erases `(s0,k0)` from the plateau at level `J+J1`.  The above-pivot
theorem proves the same erasure for the finite set of introduced labels with
level `> J`, giving a single Nat-valued same-domain progress measure.

## Source Reference

Aoyagi PDF p. 16 for Case 1(1), where the old selected variable is lowered
from level `J+J1` to level `J` while the branch stays over `(S,J)`.

## Dependencies

- `introducedLabelFinset`
- `IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData`
- `IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_levelMoveData`
- `Case1SelectedOldSuppliedSameDomainBoundary`

The theorem intentionally consumes level-move data rather than
`Case1SelectedOldLoweredRecurrenceBoundary`, because strict plateau decrease
needs per-label level preservation away from the selected old label.

## Nonclaims

No Case 1(2) progress theorem, no introduced-label support growth, no chart
construction, no source-production payload, no full branch termination, no
normal crossings, no pole order, and no RLCT is proved.

## Reproduction and Review

Reproduction:

```text
threads/04-blow-up-certificate/reproduction-a4-case1-same-domain-plateau-progress.md
```

Review:

```text
threads/04-blow-up-certificate/review-a4-case1-same-domain-plateau-progress.md
```
