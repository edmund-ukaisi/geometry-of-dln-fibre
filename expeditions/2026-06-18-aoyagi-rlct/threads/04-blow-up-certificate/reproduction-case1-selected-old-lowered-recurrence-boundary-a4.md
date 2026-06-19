# A4 Case 1(1) Selected-Old Lowered Recurrence Boundary

Status: reproduced a supplied source-facing recurrence boundary.

## Source Situation

Case 1(1) lowers the selected old label `(s0,k0)` from level `J+J1` to level
`J`.  The previous checkpoint proved the pure recurrence calculation using a
supplied base recurrence.  This checkpoint packages the source-facing boundary
that uses that calculation with recurrence states.

## Boundary Data

Assume two recurrence states over the same introduced-label domain `(S,J)`:

```text
pre  : before lowering the selected old level,
post : after lowering the selected old level.
```

Assume a supplied base recurrence `baseStep` with the selected old factor kept
separate, and a selected old scalar `u = u_(s0,k0)`, such that

```text
pre.step  = mulStepAt(baseStep, u, J+J1),
post.step = mulStepAt(baseStep, u, J).
```

The boundary also carries the already proved same-domain exponent boundary for
Case 1(1), so the recurrence-weight projection and exponent update projection
remain tied to the same first-jump and selected-label data.

## Calculation

For every residual row `i`, the row level is active:

```text
J+1 <= rowLevel(i).
```

Therefore the pure recurrence lemma gives

```text
case1SelectedOldPostWeight(strip,u,pre.weight)(i)
  = post.weight(rowLevel(i)).
```

Here `strip(i)` is the Case 1 strip condition

```text
rowLevel(i) <= J+J1.
```

Combining this with the already proved source-coordinate row-strip identity
gives

```text
diag(pre.weight) * D_source = diag(post.weight) * D_post.
```

This is now stated in recurrence-state notation, but the source interpretation
of `baseStep`, `pre`, and `post` remains supplied.

## Caveats

- This does not construct the selected-old chart.
- This does not derive `baseStep` from arbitrary source recurrence data.
- This does not prove that coordinates produce the recurrence post-state.
- This does not introduce `(S,J+1)` and does not use the displayed Case 1(2)
  pivot.
- This does not assert `Q/P`, chart coverage, regularity, Jacobian, normal
  crossings, RLCT extraction, or a transition invariant.
