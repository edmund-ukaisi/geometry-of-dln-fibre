# A4 Case 1(1) Selected-Old Unit Boundary from Concrete Level Move

Status: reproduced as a thin boundary-instantiation target and Lean-proved.

## Source Situation

Aoyagi Case 1(1), PDF p. 16, uses the selected old exceptional variable
`u_(s0,k0)` as the chart denominator.  The branch stays over the same
introduced-label domain `(S,J)`: the selected old label's recurrence level is
lowered from `J+J1` to `J`, and no new label `(S,J+1)` is introduced.

The finite Case 1 center already has a selected-old chart token

```text
Sum.inl () : Case1CenterGenerator.
```

This token is chart-family bookkeeping only.  The source label `(s0,k0)` and
its first-jump facts still come from the same-domain selected-old boundary.

## Boundary Assembly

Assume:

```text
pre : recurrence state over (S,J),
sameDomain : Case1SelectedOldSuppliedSameDomainBoundary over pre.level,
chartFamily : Case1CenterChartFamilyBoundary.
```

The concrete recurrence post-state is:

```text
post = pre.case1SelectedOldLevelMove(s0,k0),
u = pre.var(s0,k0),
baseStep = pre.erasedStep(s0,k0).
```

From the previous checkpoints:

1. `sameDomain` gives selected introducedness and
   `pre.level(s0,k0)=J+J1`.
2. `case1SelectedOldLevelMove` gives a post-state with selected level `J`,
   unchanged recurrence-label variables, and unchanged non-selected levels.
3. The erased-base model derives:

```text
pre.step  = mulStepAt(baseStep,u,J+J1),
post.step = mulStepAt(baseStep,u,J).
```

Thus the concrete post-state instantiates
`Case1SelectedOldLoweredRecurrenceBoundary`.

Adding the supplied finite chart-family boundary gives a
`Case1SelectedOldUnitSuppliedChartFamilyBoundary` with the concrete choices
above.  All existing projections of the Unit boundary then apply to this
canonical recurrence-state witness:

- selected introducedness and selected level;
- selected-old finite center membership;
- supplied chart and transition regularity;
- finite selected-entry principalization by `u`;
- pre/post recurrence source-coordinate identities;
- same-domain exponent-certificate update.

## Caveats

- This is a boundary constructor, not a chart construction theorem.
- The supplied `chartFamily` still carries chart regularity and transition
  regularity assumptions.
- The `Unit` token still does not identify `(s0,k0)` by itself.
- It stays over `(S,J)` and does not introduce `(S,J+1)`.
- It does not use Case 1(2), the displayed pivot `u_(S,J+1)`, or `Q/P`.
- It does not prove atlas coverage, regularity from raw coordinates,
  Jacobian accounting, normal crossings, RLCT extraction, or the full
  transition invariant.
