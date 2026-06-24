# Statement card - A4 Case 1 selected-old concrete source-pullback state

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_level`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_var_selected`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_var_of_ne`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.of_concreteSourcePullback`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_step_eq_mulStepAt_of_firstJump`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.of_case1SelectedOldSourcePullback`

## Statement

Given a factored-base introduced-label recurrence state and a selected old
introduced label `(s0,k0)`, the concrete source-pullback recurrence state keeps
all levels fixed, replaces the selected recurrence-label variable by
`u * factoredBase.var s0 k0`, and keeps every other recurrence-label variable
unchanged.

This concrete state satisfies the existing abstract
`Case1SelectedOldFactoredBaseData` package.  Under the already supplied
first-jump hypotheses, its recurrence factor function is

```text
mulStepAt factoredBase.step u (J+J1).
```

The displayed Case 1(2) selected-old pullback boundary can therefore use this
concrete source state instead of a separately supplied `source` recurrence
state.

## Proved

- The concrete state has the same level map as `factoredBase`.
- Its selected variable is `u * factoredBase.var s0 k0`.
- Its non-selected introduced variables agree with `factoredBase`.
- The concrete state supplies `Case1SelectedOldFactoredBaseData`.
- The first-jump recurrence is the single-factor insertion
  `mulStepAt factoredBase.step u (J+J1)`.
- A row-strip pullback boundary constructor instantiates the abstract source
  field with this concrete state.

## Assumed

- The selected old label is introduced, supplied either directly or through the
  existing first-jump data in the row-strip handoff.
- The row-strip boundary wrapper still assumes the local handoff, post-state,
  exponent post-data, and finite matrix transition data already packaged by
  `Case1DisplayedRowStripSuppliedTransitionBoundary`.

## Cited

- None in Lean.  This is finite recurrence bookkeeping and finite-product
  algebra.

## Deferred

- Construction of `factoredBase`, displayed row-strip post-data, exponent
  post-data, raw source-coordinate provenance, the selected-old chart, chart
  coverage, transition regularity, analytic Jacobian/volume control,
  normal-crossing certificate production, termination, pole order, and RLCT
  extraction.

## Review

- xhigh reviewer `Schrodinger` passed the slice with no blocking findings.

## Verification

- `lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `lean/scripts/lb DLNFibre` passed.
- `lean/scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
