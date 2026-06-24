# A4 Case 1(2) Selected-Old Concrete Source-Pullback State

Status: reproduced and formalised the elementary recurrence-state source
pullback behind the selected-old substitution.  This is not a selected-old
chart construction theorem.

## Source Situation

In Aoyagi Case 1(2), the old selected exceptional variable is rewritten on the
selected-old chart as

```text
old = u * old'.
```

The row-strip transition already works with a `factoredBase` recurrence state,
where the selected old recurrence-label variable is the residual variable
`old'`.  The source-facing recurrence state should therefore be the same finite
introduced-label recurrence, except that the selected label `(s0,k0)` carries
`u * old'`.

## Pen-And-Paper Calculation

Let `factoredBase` be an introduced-label recurrence state at `(S,J)`.
Define `source` by

```text
source.level(s,k) = factoredBase.level(s,k),

source.var(s,k) =
  u * factoredBase.var(s0,k0),  if (s,k) = (s0,k0),
  factoredBase.var(s,k),        otherwise.
```

If `(s0,k0)` is introduced, then this source state satisfies exactly the
selected-old source-pullback data:

```text
source.level = factoredBase.level,
source.var(s0,k0) = u * factoredBase.var(s0,k0),
source.var(s,k) = factoredBase.var(s,k) for every other introduced label.
```

Consequently the existing finite-product lemma applies.  At the selected
level, the filtered product acquires the single multiplicative factor `u`; at
every other level the filtered product is unchanged.  If the first-jump data
places `(s0,k0)` at level `J+J1`, then

```text
source.step = mulStepAt factoredBase.step u (J+J1).
```

No additional matrix algebra is used.  This is the recurrence-variable
substitution corresponding to `old = u * old'`.

## Lean Boundary

Lean now defines the concrete pulled-back recurrence state:

```text
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback
```

and proves:

```text
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_level
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_var_selected
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_var_of_ne
IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.of_concreteSourcePullback
IntroducedLabelRecurrenceState.case1SelectedOldSourcePullback_step_eq_mulStepAt_of_firstJump
```

The displayed row-strip pullback boundary can now be instantiated with the
concrete source state:

```text
Case1DisplayedRowStripSelectedOldPullbackBoundary.of_case1SelectedOldSourcePullback
```

## Caveats

- This does not construct `factoredBase`, the displayed row-strip post-state,
  exponent post-data, or the local handoff.
- This does not construct the selected-old affine chart.
- This does not identify the finite `Unit` center token with a source label by
  itself.
- This does not prove raw-coordinate provenance of `old = u * old'`.
- This does not prove chart coverage, transition regularity, Jacobian or volume
  arithmetic, normal crossings, termination, pole order, or RLCT extraction.
