# A4 Case 1(1) Selected-Old Concrete Level Move

Status: reproduced as a narrow recurrence-state post-data target before Lean
formalisation.

## Source Situation

Aoyagi Case 1 fixes an already introduced old exceptional variable
`u_(s0,k0)` whose selected level is

```text
tilde_t_(s0,k0) = J+J1.
```

In Case 1(1), PDF p. 16 records the selected-old branch:

```text
t'_(s0,k0)^(S) = t'_(s0,k0)^(S+1) = ... = t'_(s0,k0)^(L) = J,
tilde_t'_(s0,k0) = J.
```

The branch stays over the same introduced-label domain `(S,J)`.  It does not
introduce the Case 1(2) displayed pivot `(S,J+1)`.

## Concrete Recurrence State

Given a recurrence state `pre` over `(S,J)`, define a same-domain state

```text
post = pre.case1SelectedOldLevelMove(s0,k0)
```

where `J` is the pivot level carried by the state type.  The definition changes
only the selected label's recurrence level:

```text
post.level(s0,k0) = J,
post.level(s,k) = pre.level(s,k)      for (s,k) != (s0,k0),
post.var(s,k) = pre.var(s,k)          for all (s,k).
```

The last line concerns the recurrence-label variables only.  The residual
matrix coordinates in the selected-old chart are still rescaled on the row
strip, as recorded by the separate row-strip source-coordinate identity.

If the selected old label is introduced and

```text
pre.level(s0,k0) = J+J1,
```

then this concrete post-state supplies the moved-level data with selected
scalar

```text
u = pre.var(s0,k0).
```

Indeed:

```text
pre.level(s0,k0)  = J+J1,
post.level(s0,k0) = J,
pre.var(s0,k0)    = u,
post.var(s0,k0)   = u,
```

and all non-selected introduced labels keep their level and variable data.

## Connection to the Erased Base

The previous erased-base checkpoint then applies directly.  Since the
non-selected introduced-label data are unchanged, the erased recurrence
factor is unchanged:

```text
post.erasedStep(s0,k0) = pre.erasedStep(s0,k0).
```

Therefore:

```text
pre.step  = mulStepAt(pre.erasedStep(s0,k0), pre.var(s0,k0), J+J1),
post.step = mulStepAt(pre.erasedStep(s0,k0), pre.var(s0,k0), J).
```

This gives a concrete same-domain recurrence-state instantiation of the
lowered-recurrence boundary from first-jump data.

## Caveats

- This is recurrence-state bookkeeping only.
- It does not construct the selected-old blow-up chart from raw coordinates.
- It does not prove that source coordinates produce this post-state.
- It does not infer `(s0,k0)` from the `Unit` finite-center token.
- It stays over `(S,J)` and does not introduce `(S,J+1)`.
- It does not use Case 1(2), the displayed pivot `u_(S,J+1)`, or `Q/P`.
- It does not prove chart coverage, regularity from coordinates, Jacobians,
  normal crossings, RLCT extraction, or the full transition invariant.
