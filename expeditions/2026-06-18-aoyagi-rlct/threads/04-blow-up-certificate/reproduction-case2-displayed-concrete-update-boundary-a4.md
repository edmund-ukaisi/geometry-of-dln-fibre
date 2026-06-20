# A4 Case 2 Displayed Concrete-Update Boundary

Status: reproduced a displayed top-left supplied boundary with concrete
recurrence and corrected exponent assignments.

## Source Situation

Aoyagi's Case 2 displayed chart is the top-left residual-block chart

```text
d_(J+1,J+1) = u_(S,J+1).
```

The residual row range is

```text
J+1 <= i <= M(S),
```

where `M(S)` is the prefix minimum, while the residual column range is

```text
J+1 <= j <= M^(S+1),
```

where `M^(S+1)` is the actual reduced layer width. The source continuation
condition

```text
J+1 <= M(S+1)
```

therefore places the displayed pivot `(J+1,J+1)` in the residual-block center:
it gives both `J+1 <= M(S)` and `J+1 <= M^(S+1)`.

## Boundary / Reproduction

The previous supplied source-selected pivot boundary accepted an arbitrary
supplied pivot `p` and supplied recurrence/exponent post-data. For the
displayed top-left chart, two of those supplied choices can be made concrete
without constructing the chart itself.

The recurrence successor is the named assignment

```text
pre.case2Succ u.
```

It adds only the new label `(S,J+1)`, assigns it level `J`, assigns it variable
`u`, and leaves all old introduced labels unchanged. The old-label
preservation is justified because `(S,J+1)` is not introduced at state
`(S,J)`.

The corrected exponent successor is the selected-label override

```text
t'          = update (S,J+1) (correctedCase2PivotVector n S J) t
numerator' = update (S,J+1) ((M(S)-J)(M^(S+1)-J)) numerator
leastValue'= update (S,J+1) J leastValue.
```

This is the corrected prefix-minimum Case 2 assignment. It does not use the
PDF's printed actual-width vector in the incompatible cases isolated by the
printed-mismatch boundary.

The displayed boundary packages:

- source continuation data;
- the displayed pivot membership proof;
- pre-state exponent certificates;
- the level/least-value bridge and Case 2 least-value gap;
- recurrence post-data, either supplied or concretely `case2Succ`;
- corrected exponent post-data, either supplied or concretely `updateSelected`;
- the supplied finite Case 2 chart-family boundary.

It projects back to the source-selected boundary at `p=(J+1,J+1)`, and also
projects the source-coordinate displayed `Q/P` identity by restricting source
residual and following-factor functions to the residual block.

## Scope / Caveats

- This is about the source-displayed top-left Case 2 pivot only.
- The concrete `case2Succ` and `updateSelected` assignments are recurrence and
  exponent assignments, not chart-produced data.
- `ChartRegular` and `TransitionRegular` remain supplied predicates.
- The displayed source-coordinate `Q/P` projection uses already-normalized
  local algebra and supplied recurrence gap/post-data hypotheses.
- The printed Case 2 vector mismatch remains unresolved by this checkpoint.
- This proves no affine blow-up atlas, chart coverage, coordinate regularity,
  chart-produced post-data, Jacobian, normal crossing, RLCT extraction,
  termination, source comparability theorem, or full transition invariant.
