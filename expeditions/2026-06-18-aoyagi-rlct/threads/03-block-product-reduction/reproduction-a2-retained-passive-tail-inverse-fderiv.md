# Reproduction - A2 Retained-Passive Tail-Inverse Frechet Derivative

Date: 2026-06-27.

Status: pen-and-paper reproduction for the inverse derivative of the retained-
passive top-left tail.  This identifies the derivative of the inverse tail in
terms of the actual Frechet derivative of the tail map; it does not compute
that tail derivative as a recursive product.

## Setup

For a retained-passive raw tuple `z`, define

```text
Tfun(y) = retainedPassiveA1TailAfterFirst (ofTopologyTuple y).A1seed,
Tail    = Tfun(z),
dTail   = d(Tfun)_z(v).
```

The target is

```text
d_y(Tfun(y)^{-1})_z(v)
  = - Tail^{-1} * dTail * Tail^{-1}.
```

## Unit Hypothesis

The determinant-chart hypothesis gives determinant units for the passive
top-left factors `A1seed_p`, `p != 0`.  The already landed tail-unit lemma gives

```text
IsUnit det(Tail).
```

The `Ctop` determinant-unit part of the chart is not used in this inverse
identity.

## Chain Rule

Matrix inversion is Frechet differentiable at `Tail` with derivative

```text
H |-> - Tail^{-1} * H * Tail^{-1}.
```

Composing this derivative with the differentiable tail map `Tfun` gives

```text
d_y(Tfun(y)^{-1})_z
  = (H |-> - Tail^{-1} * H * Tail^{-1}) ∘ d(Tfun)_z.
```

Applying to `v` yields

```text
d_y(Tfun(y)^{-1})_z(v)
  = - Tail^{-1} * dTail * Tail^{-1}.
```

The order of multiplication matters: `dTail` is the middle factor.

## Ctop Sign

The previous Ctop source-staged successor bridge has the term

```text
- d_y(Tfun(y)^{-1})_z(v) * coord.Ctop.
```

After substitution this becomes

```text
+ Tail^{-1} * dTail * Tail^{-1} * coord.Ctop.
```

This sign change is part of the strengthened Ctop theorem.

## Endpoint Case

For `M = 0`, the tail after the first edge is the empty product, hence `Tail=1`
and the displayed inverse-derivative identity remains valid.  This slice does
not need a separate endpoint simplification and does not assert that `dTail=0`
as a standalone theorem.

## Kill Conditions

- If `dTail` is described as an explicit source-staged product derivative, the
  statement overclaims.  Here `dTail` is only `(fderiv Tfun z) v`.
- If the derivative is written with `dTail` outside the two inverse factors, the
  matrix multiplication order is wrong.
- If the Ctop bridge keeps a negative sign after substituting the inverse
  derivative, the sign is wrong.
- If the determinant-chart hypothesis is removed, the inverse derivative of
  matrix inversion is not justified at the required point.

## Nonclaims

No recursive product formula for `dTail`, no full `Ctop` source staging, no
`F3` or terminal-top statement, no target-side `LinearEquiv`, no determinant-
one shear, no actual derivative determinant equality, no measure theorem, no
normal crossings, no pole order, and no RLCT statement is proved by this slice.
