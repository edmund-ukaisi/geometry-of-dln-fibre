# A4 Case 1(1) Selected-Old Erased-Base Source Model

Status: reproduced and formalised a finite-product recurrence source model.

## Source Situation

On PDF pp. 15-16, Aoyagi Case 1 chooses an old exceptional variable
`u = u_(s0,k0)` with selected level

```text
tilde_t_(s0,k0) = J+J1.
```

In Case 1(1), the selected-old chart divides the row strip

```text
J+1 <= i <= J+J1
```

by this same old variable and resets the selected label's tail levels so that
its new selected level is `J`.  The introduced-label domain remains `(S,J)`;
no new `(S,J+1)` label is introduced in this branch.

## Erased-Label Base

Let `a = (s0,k0)` and let `labels` be the finite introduced-label set at
state `(S,J)`.  Define the base recurrence factor by erasing the selected
label:

```text
baseStep(r) =
  product over p in labels \ {a} with level(p)=r of var(p).
```

This is the correct base object: it is not obtained by cancellation from
`pre.step`, and it does not contain a residual selected old factor.

For any recurrence state `state` in which `a` is introduced, finite product
insert/erase bookkeeping gives

```text
state.step = mulStepAt(state.erasedStep(a), state.var(a), state.level(a)).
```

Indeed, at `r = level(a)` the selected factor is inserted into the filtered
product.  At any other `r`, the selected label is absent from the filtered
product, so the erased and unerased products agree.

## Case 1(1) Move

Assume recurrence states `pre` and `post` over the same `(S,J)` label domain
with:

```text
pre.level(a)  = J+J1,
post.level(a) = J,
pre.var(a)    = u,
post.var(a)   = u,
```

and for every introduced non-selected label `p != a`,

```text
post.level(p) = pre.level(p),
post.var(p)   = pre.var(p).
```

Then the erased base recurrence is unchanged:

```text
post.erasedStep(a) = pre.erasedStep(a).
```

Reinserting the selected label into the erased base therefore gives

```text
pre.step  = mulStepAt(pre.erasedStep(a), u, J+J1),
post.step = mulStepAt(pre.erasedStep(a), u, J).
```

These are exactly the two recurrence equalities previously supplied to the
lowered-recurrence boundary.

## Row-Weight Calculation

For residual rows, `i >= J+1`.  The pure recurrence lemma already proves:

```text
if i <= J+J1:
  monomialRec(pre.step,i)  = monomialRec(baseStep,i),
  monomialRec(post.step,i) = u * monomialRec(baseStep,i);

if i > J+J1:
  monomialRec(pre.step,i)  = u * monomialRec(baseStep,i),
  monomialRec(post.step,i) = u * monomialRec(baseStep,i).
```

Thus multiplying the divided row strip by source entries is equivalent to
absorbing the selected old factor into the post recurrence weights:

```text
diag(pre.weight) * D_source = diag(post.weight) * D_post.
```

The new Lean constructor only instantiates the already existing
`Case1SelectedOldLoweredRecurrenceBoundary` with

```text
baseStep = pre.erasedStep(s0,k0).
```

## Caveats

- This is recurrence finite-product bookkeeping only.
- It does not construct the selected-old chart from raw coordinates.
- It does not infer `(s0,k0)` from the `Unit` finite-center token.
- It remains over `(S,J)` and does not introduce `(S,J+1)`.
- It does not use Case 1(2), the displayed pivot `u_(S,J+1)`, or `Q/P`.
- It does not prove chart coverage, transition regularity, Jacobians, normal
  crossings, RLCT extraction, or the full blow-up transition invariant.
