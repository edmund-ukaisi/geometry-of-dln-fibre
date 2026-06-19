# A4 Case 2 Introduced-Label Gap

Status: reproduced finite-domain bridge from Lean's introduced-label predicate to
the displayed Case 2 label-product gap; independent xhigh check saved at
`review-case2-introduced-label-gap-a4.md`.

## Source Facts

Aoyagi's inductive state records the active exceptional variables as

```text
u_(s,k), 1 <= s <= S-1, 1 <= k <= M^(s+1),
u_(S,k), 1 <= k <= J.
```

The diagonal monomials satisfy the recurrence

```text
b_0 = 1,
b_i = (product over tilde_t_(s,k)=i-1 of u_(s,k)) * b_(i-1).
```

This is the recurrence display in the inductive statement on PDF p. 15. In
Case 2, Aoyagi assumes

```text
b_(J+1) = ... = b_(M(S)),
```

equivalently there are no active labels with
`tilde_t = J+1, ..., M(S)-1`; see PDF pp. 19-20.

## Reproduction

Lean already models an introduced label at state `(S,J)` by

```text
actualWidthLabel L n s k
and
(s < S or (s = S and k <= J)).
```

Since `1 <= s <= L` and `1 <= k <= n_(s+1)` are finite ranges, the introduced
labels can be enumerated as a finite sigma-domain

```text
(s,k) with 1 <= s <= L, 1 <= k <= n_(s+1),
and (s < S or (s = S and k <= J)).
```

If the supplied level map satisfies the Case 2 gap on every introduced label,

```text
for every introduced (s,k),
not (J+1 <= level(s,k) < mu_S),
```

then the finite product over introduced labels with `level=r` is empty for
every `J+1 <= r < mu_S`. Therefore the existing label-product bridge applies
with the supplied finite label set instantiated to the introduced-label finite
domain.

## Scope

This bridge removes one purely finite mismatch: the previous theorem accepted an
arbitrary supplied `labels : Finset beta`; the new theorem uses the finite set
defined by Lean's `introducedLabel` predicate.

It still assumes:

- the level map is the recurrence level `tilde_t`,
- the variable map assigns the recurrence variable `u_(s,k)`,
- the introduced-label gap holds,
- the row weights are represented by the monomial recurrence using this product.

It does not prove the recursive transition invariant, the source recurrence
assignment, arbitrary-pivot chart coverage, chart regularity/Jacobian, exponent
updates, termination, normal crossings, or RLCT extraction.

## Reproduction Check

- Checker/path/verdict: xhigh source/pen-and-paper and Lean/API reviews saved at
  `review-case2-introduced-label-gap-a4.md`; verdict is sound as a conditional
  finite introduced-label-domain bridge, with the invariant caveats above.
