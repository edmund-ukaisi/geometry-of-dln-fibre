# Reproduction - A4 Case 1(1) same-domain plateau progress

Date: 2026-06-30.

Status: controller pen-and-paper reproduction before Lean.

## Question

What finite quantity decreases in Aoyagi Case 1(1)?

It is not the introduced-label support.  Case 1(1) stays on the same
introduced-label domain `(S,J)`.  The decreasing quantity is the count of
already introduced old labels whose current recurrence level is still above the
pivot level `J`; more locally, at the first jumped level `J+J1`, the selected
old label is removed from that exact plateau.

## Source Situation

Aoyagi PDF p. 16 chooses the old exceptional variable `u_(s,k)` itself as the
Case 1(1) denominator.  The selected old label is already introduced at
`(S,J)` and has level

```text
level(s0,k0) = J+J1,
```

with `1 <= J1`.  The Case 1 first-jump hypotheses say there are no introduced
labels at levels strictly between `J` and `J+J1`.

In Case 1(1), the branch lowers that selected old label to level `J` and leaves
all non-selected introduced labels in the same domain:

```text
post.level(s0,k0) = J,
post.level(s,k) = pre.level(s,k)  for (s,k) != (s0,k0).
```

## Finite Progress Calculation

Let

```text
Plateau_r(pre)
  = { introduced labels p at (S,J) | pre.level(p)=r },

Above(pre)
  = { introduced labels p at (S,J) | J < pre.level(p) }.
```

For the supplied Case 1(1) selected-old level move:

```text
Plateau_(J+J1)(post) = Plateau_(J+J1)(pre) \ {(s0,k0)}.
```

The selected label belongs to the pre-plateau because it is introduced and has
level `J+J1`.  It does not belong to the post-plateau because its post level is
`J` and `J1>0`.  Every non-selected introduced label has the same level before
and after the move.

The same argument gives the more usable same-domain measure:

```text
Above(post) = Above(pre) \ {(s0,k0)}.
```

Therefore both finite cardinalities strictly decrease.

## Nonclaims

This does not cover Case 1(2), does not prove introduced-label support growth,
does not construct the selected-old chart or source coordinates, does not infer
the selected old label from the `Unit` chart token, does not prove source
production, full branch termination, normal crossings, pole order, or RLCT.
