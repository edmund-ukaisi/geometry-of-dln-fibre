# A4 Case 1(2) Displayed Row-Strip Local Handoff

Status: reproduced the local handoff combining the displayed source-order
identity, the factored-base recurrence post-data, and the new-label exponent
post-data. This is not a full transition theorem.

## Source Situation

On Aoyagi PDF p. 17, Case 1(2) starts from a selected old exceptional
variable at level

```text
h = J + J1.
```

The chart factors this old variable as `old = u * old'` and then introduces a
fresh label `(S,J+1)`. The displayed row strip is the residual-row range

```text
J+1 <= i <= J+J1.
```

The new label has level `J`, so with the recurrence convention

```text
b_(r+1) = step_r * b_r
```

it affects every residual row from `J+1` onward. The old selected factor at
level `J+J1` affects rows only from `J+J1+1` onward.

## Width Bookkeeping

The row and column bounds remain separate.

Residual rows live in

```text
J+1 <= i <= prefixMinNat n S.
```

Residual columns live in the actual source width

```text
J+1 <= j <= n(S+1).
```

The first-jump package supplies `1 <= J1` and
`J+J1 < prefixMinNat n S`, hence `J+1 <= prefixMinNat n S`. Together with the
actual column bound `J+1 <= n(S+1)`, this gives the displayed continuation
bound

```text
J+1 <= prefixMinNat n (S+1).
```

The exponent increment uses the actual width:

```text
J1 * (n(S+1) - J).
```

It must not be rewritten as a prefix-minimum expression.

## Pen-And-Paper Calculation

Let `factoredBase.step` be the recurrence after replacing the old selected
variable by the residual old variable `old'`. The original source recurrence
after substituting `old = u * old'` is

```text
mulStepAt factoredBase.step u (J+J1).
```

For a residual row of level `i`:

```text
J+1 <= i <= J+J1:
  sourceWeight_i = factoredBase.weight_i,

J+J1+1 <= i:
  sourceWeight_i = u * factoredBase.weight_i.
```

The displayed source matrix contributes the factor `u` exactly on the strip
rows and leaves the lower residual rows unchanged. Therefore

```text
diagonal sourceWeight * rowStripSourceMatrix
  =
diagonal (u * factoredBase.weight) * normalizedMatrix.
```

Supplied recurrence post-data then rewrites

```text
post.weight i = u * factoredBase.weight i
```

for every residual row `i >= J+1`, because the fresh label `(S,J+1)` has been
inserted at level `J`.

On the exponent side, the supplied Case 1 displayed row-strip post-data
preserves old introduced labels and assigns the fresh label

```text
vector      = lowerTailVector (t s0 k0) S J,
numerator   = numerator s0 k0 + J1 * (n(S+1) - J),
least value = J.
```

The lower-tail certificate still requires the old selected label certificate,
the level/least-value bridge, the flat-tail invariant above the pivot, and
`2 <= S <= L`.

## Lean Boundary

Lean now has a local supplied boundary:

```text
Case1DisplayedRowStripSuppliedTransitionBoundary
```

Its source-order projection uses the original source recurrence on the left
diagonal:

```text
monomialRec (mulStepAt factoredBase.step u (J+J1))
```

and supplied post-state recurrence weights on the right. Its exponent
projection extends the introduced-label exponent certificate package from
state `(S,J)` to `(S,J+1)`.

## Caveats

- This does not construct the factored-base recurrence state from the original
  pre-chart state.
- This does not prove hidden old-label source validity.
- This does not prove that a chart produces the supplied recurrence or
  exponent post-data.
- This does not prove chart coverage, chart regularity, transition regularity,
  a Jacobian formula, normal crossings, or RLCT extraction.
