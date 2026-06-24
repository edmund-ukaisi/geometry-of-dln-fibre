# Review - A4 Case 1 selected-old concrete source-pullback state

Reviewer: xhigh subagent `Schrodinger`

Status: passed after documentation consistency fix.

## Findings

- No blocking Lean, mathematics, or source-fidelity findings.
- Low documentation issue: `thread.md` referenced this review artifact before
  it existed, while the statement card still said the review was pending.  This
  file resolves that mismatch, and the statement card now records the passed
  review.

## Reviewed Lean Names

```text
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_level
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_var_selected
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_var_of_ne
IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.of_concreteSourcePullback
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_step_eq_mulStepAt_of_firstJump
Case1DisplayedRowStripSelectedOldPullbackBoundary.of_case1SelectedOldSourcePullback
```

## Boundary Check

The concrete recurrence state only preserves `factoredBase.level` and changes
the selected recurrence variable to `u * factoredBase.var s0 k0`.  The
concrete-data theorem still requires selected-label introducedness, and the
first-jump theorem proves only the recurrence equality
`step = mulStepAt factoredBase.step u (J+J1)`.

The row-strip wrapper still takes the local handoff as supplied data and uses
it only to instantiate the concrete `sourcePullback`.  It does not construct
the selected-old chart, raw source-coordinate provenance, post-state, exponent
data, normal crossings, pole order, or RLCT extraction.

## Verification Observed by Controller

- `lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `lean/scripts/lb DLNFibre` passed.
- `lean/scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
