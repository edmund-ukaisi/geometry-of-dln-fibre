# A4 Case 2 Displayed Source-Chart Boundary Constructor

Status: reproduced the thin supplied-boundary constructor which uses Aoyagi's
displayed source-chart pivot value as the Case 2 boundary scalar.  This is a
packaging step, not new chart production.

## Source Anchor

On PDF pp. 19-21 Aoyagi's displayed Case 2 chart selects the top-left
residual-block entry:

```text
d_(J+1,J+1) = u_(S,J+1),
d_ij = u_(S,J+1) d'_ij    off the selected entry.
```

The same displayed calculation then treats `u_(S,J+1)` as the new recurrence
variable and records the Case 2 update of the exceptional data.  In the
expedition's corrected certificate, the exponent update for the new label
`(S,J+1)` is the prefix-minimum update already used by the displayed supplied
boundary:

```text
vector = correctedCase2PivotVector n S J,
numerator = (M(S)-J)(M^(S+1)-J),
least value = J.
```

## Pen-And-Paper Reproduction

Let

```text
p =
  case2DisplayedSourceChartMap n hS hcont u residual (J+1,J+1).
```

By the definition of the displayed source chart map, the selected entry maps
to the selected variable:

```text
p = u.
```

The concrete displayed-boundary constructor already packages the supplied
Case 2 boundary with scalar `v` as follows:

```text
post recurrence state = pre.case2Succ v,
exponent post-data = corrected updateSelected data,
chart-family data = supplied Case2ResidualBlockChartFamilyBoundary.
```

Therefore substituting `v = p` gives the same supplied boundary with

```text
post = pre.case2Succ p,
scalar = p.
```

Equivalently, the recurrence post-data field can be checked directly: the
previous recurrence theorem says

```text
pre.case2Succ u
```

is a Case 2 supplied post-state for the displayed pivot value
`case2DisplayedSourceChartMap(...)(J+1,J+1)`. Since that pivot value is
definitionally `u`, the post-state in the target is exactly

```text
pre.case2Succ (case2DisplayedSourceChartMap(...)(J+1,J+1)).
```

All remaining fields are unchanged from the displayed concrete-update
boundary:

- `hS`, `hSL`, and `hcont` give the stage and continuation hypotheses;
- `exponentPre`, `levelInv`, and `leastValueGap` are supplied pre-state
  certificates;
- `Case2CorrectedExponentPostData.updateSelected` supplies the corrected
  selected-label exponent post-data;
- `chartFamily` supplies the chart and transition regularity predicates.

## Boundaries

- The displayed source chart map is used only through its pivot value.
- The theorem does not derive post-data from all chart coordinates.
- The exponent post-data are still the corrected selected-label overrides, not
  Jacobian-derived data.
- Chart regularity and transition regularity remain supplied by
  `chartFamily`.
- No atlas coverage, coordinate regularity from coordinates, Jacobian/volume
  arithmetic, normal crossings, RLCT extraction, termination, transition
  invariant, or printed-vector repair is proved.
