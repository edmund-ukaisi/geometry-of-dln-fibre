# A4 Case 1(2) Selected-Old Source Substitution

Status: reproduced the elementary recurrence substitution boundary for the
hidden old selected label. This is not a chart construction theorem.

## Source Situation

In Aoyagi Case 1(2), the selected old exceptional variable has source level

```text
h = J + J1.
```

The selected-old chart writes the old variable as

```text
old = u * old'.
```

The factored-base recurrence is the recurrence after replacing `old` by the
residual variable `old'`. The substituted source recurrence is the original
source recurrence after applying `old = u * old'`.

This source recurrence is not the raw pre-chart coordinate recurrence. It is
already pulled back to the selected-old chart coordinates.

## Pen-And-Paper Calculation

Let `factoredBase.step r` be the product of all introduced variables of level
`r`, using `old'` at the selected old label. Let `source.step r` be the same
finite product after replacing the selected old variable by `u * old'`.

Assume:

```text
selected label (s0,k0) is introduced,
source.level = factoredBase.level,
factoredBase.level s0 k0 = J + J1,
source.var s0 k0 = u * factoredBase.var s0 k0,
source.var s k = factoredBase.var s k for all other introduced labels.
```

Then, at level `J+J1`, commutativity lets the selected factor be pulled out of
the finite product:

```text
source.step (J+J1) = u * factoredBase.step (J+J1).
```

At any other level, the selected label is not in the filtered product, and all
variables in the filtered product agree:

```text
source.step r = factoredBase.step r,    r != J+J1.
```

Therefore

```text
source.step = mulStepAt factoredBase.step u (J+J1).
```

By the recurrence convention `b_(r+1)=step_r*b_r`, this means the old selected
factor affects source row weights only from row `J+J1+1` onward.

## Lean Boundary

Lean now proves the generic same-domain selected-variable update:

```text
levelProductStep_eq_mulStepAt_of_updateSelected
```

and packages the Case 1(2) recurrence-state assumptions as

```text
IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.
```

The first-jump wrapper proves:

```text
source.step = mulStepAt factoredBase.step u (J+J1).
```

The row-strip corollary rewrites the row-strip old-weight convention as the
substituted source recurrence weights on residual rows.

## Caveats

- This does not construct the selected-old chart.
- This does not prove the hidden old label exists from the `Unit` center
  generator.
- This does not construct the factored-base state.
- This does not prove recurrence or exponent post-data production.
- This does not prove chart coverage, regularity, Jacobian accounting, normal
  crossings, or RLCT extraction.
