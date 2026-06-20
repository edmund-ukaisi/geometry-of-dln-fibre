# A4 Case 2 Stage-Relabel Domain Audit

Status: reproduced the finite introduced-label domain comparison around
Aoyagi's terminal Case 2 branch.  This is not an `S+1` transition theorem.

## Source Anchor

On PDF pp. 21-22, after the displayed Case 2 `Q/P` calculation, Aoyagi
distinguishes the next `J`-continuation from the terminal branch and then
rewrites the product as the inductive statement with `S` increased by one.

Lean's introduced-label domain uses actual layer widths:

```text
introducedLabel L n S J s k
  iff 1 <= s <= L, 1 <= k <= n(s+1),
      and (s < S or s = S and k <= J).
```

Therefore moving from old `(S,J+1)` to `(S+1,0)` is not automatically a
domain relabel.  It is a relabel only on the actual-width-exhausted side of
the terminal frontier.

## Pen-And-Paper Reproduction

Let

```text
muS = M(S) = prefixMinNat n S,
w   = M^(S+1) = n(S+1).
```

For `1 <= S`,

```text
M(S+1) = min(muS, w).
```

If the displayed pivot is valid and the next one is not, then

```text
J+1 <= M(S+1) and not (J+2 <= M(S+1))
```

so

```text
M(S+1) = J+1.
```

Equivalently,

```text
min(muS, w) = J+1.
```

Thus either the current prefix row side is exhausted,

```text
muS = J+1,
```

or the actual next-width column side is exhausted,

```text
w = J+1.
```

The disjunction is not exclusive.

Now compare introduced-label domains.  At old `(S,J+1)`, the introduced
labels are:

```text
all actual labels in layers s < S,
plus actual labels in layer S with k <= J+1.
```

At `(S+1,0)`, they are:

```text
all actual labels in layers s < S+1,
and no actual labels in layer S+1 because k <= 0 contradicts 1 <= k.
```

Hence the two domains are equal if the actual layer `S` has width exactly
`J+1`, i.e. if `n(S+1)=J+1`.

If instead the actual width still has a next label, `J+2 <= n(S+1)`, then
`(S,J+2)` is actual-width valid and belongs to `(S+1,0)` because `S < S+1`.
It does not belong to old `(S,J+1)` because it is a current-layer label above
the processed index.  This is the finite row-side obstruction.

## Boundaries

- The stage-domain equality is conditional on actual-width exhaustion
  `n(S+1)=J+1`.
- The frontier equality `M(S+1)=J+1` alone is insufficient: it may come from
  row-prefix exhaustion `M(S)=J+1` while actual width still has labels above
  `J+1`.
- This does not construct the `S+1` recurrence/exponent state, prove the
  terminal `D'''` block shape, construct `C'^(S+1)`, prove chart coverage,
  coordinate regularity, Jacobian arithmetic, normal crossings, RLCT
  extraction, termination, transition invariance, or repair of the printed
  Case 2 vector mismatch.
