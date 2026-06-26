# Reproduction - A2 retained-passive `A3_last` prefix target

Date: 2026-06-26.

Status: pen-and-paper follow-up to
`reproduction-a2-retained-passive-a3-last-endpoint-solve.md`.

## Setup

Continue with a nonempty retained-passive edge family with `M+1` edges.  The
explicit product tail is

```text
Tail_p =
  -(D_{p+1} * A3_p * Ctop_p^-1) + Tail_{p+1},
Tail_terminal = 0.
```

The previous rung proved the final-edge cancellation:

```text
Tail_last = G
```

whenever

```text
A3_last = -G * Ctop_last
```

and `det(Ctop_last)` is a unit.

## Earlier Signed Tail

To isolate the earlier edges without introducing a new `Finset` indexing layer,
zero the final lower-left block:

```text
A3early_p =
  A3_p     if p < last,
  0        if p = last.
```

Let

```text
EarlyTail = Tail_0(A3early).
```

Because the final block is zero, `Tail_last(A3early)=0`, and reverse induction
gives the split

```text
Tail_0(A3) = EarlyTail + Tail_last(A3).
```

Here

```text
EarlyTail = - sum_{p<last} D_{p+1} * A3_p * Ctop_p^-1.
```

Thus the unsigned earlier prefix from the coordinate-domain note is

```text
Prefix = -EarlyTail.
```

## Source Target

The retained-passive coordinate-domain note wants the active source coordinate
`F3` to be the full source tail:

```text
Tail_0(A3) = F3.
```

Since `Tail_0(A3) = EarlyTail + Tail_last(A3)`, it is enough to set

```text
Tail_last(A3) = F3 - EarlyTail.
```

By the final-edge cancellation rung, this is achieved by

```text
A3_last = -(F3 - EarlyTail) * Ctop_last.
```

Equivalently, because `EarlyTail = -Prefix`, this is the paper-facing formula

```text
A3_last = -(F3 + Prefix) * Ctop_last.
```

Then

```text
Tail_0(A3)
  = EarlyTail + (F3 - EarlyTail)
  = F3.
```

## Lean Scope

Main Lean names:

```text
retainedPassiveA3WithoutLast
retainedPassiveA3WithoutLast_last
retainedPassiveA3WithoutLast_eq_of_ne
retainedPassiveLowerLeftProductTailSum_withoutLast_last
retainedPassiveLowerLeftProductTailSum_eq_withoutLast_add_last
retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq
```

The theorem stays in recursive-tail form rather than translating to `Finset`
sums.  This matches the existing `suffixState` and `residualFactorProduct`
definitions and avoids a separate reindexing proof.

## Nonclaims

This proves finite tail algebra only.  It does not yet construct the full
retained-passive coordinate domain, does not reconstruct `A1_0` from an active
`Ctop_0`, does not prove determinant-unit neighborhoods, source-rank coverage,
source/image equality, source-measure pushforward, density/Jacobian transport,
normal crossings, pole order, or RLCT.
