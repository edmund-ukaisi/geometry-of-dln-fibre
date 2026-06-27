# Reproduction - A2 retained-passive actual derivative Ctop shear bridge

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; independent xhigh check PASS;
Lean component bridge proved.

This note is independent of the quiver-based paper.  It uses only the
retained-passive block-coordinate algebra isolated from Aoyagi's local product
reduction.

## Setup

Work in the retained-passive raw-order map

```text
raw = topologyTupleEdgeRawOrder.
```

At a tuple `z`, write

```text
data  = ofTopologyTuple z,
coord = data.toCoordinateData,
Tail  = retainedPassiveA1TailAfterFirst data.A1seed,
U     = Tail^{-1}.
```

For the first edge set

```text
A_0 = coord.solvedA1 0,
H_0 = coord.F2 (0 : Fin (M+1)).succ,
G_0 = coord.solvedA3 0,
C0  = coord.Ctop.
```

The solved first top-left block is

```text
A_0 = U * C0.
```

For a tangent vector `v`, abbreviate Frechet differentials at `z` by

```text
dU  = d(U)(v),
dC0 = d(Ctop)(v) = v.Ctop,
dH  = d(H_0)(v),
dG  = d(G_0)(v).
```

## Raw Formula

The raw `Ctop` target is the top-left block of the first edge:

```text
Y11_0 = A_0 + H_0 * G_0.
```

Substituting the first-edge solve gives

```text
Y11_0 = U * C0 + H_0 * G_0.
```

## Calculation

Differentiate:

```text
dY11_0
  = d(U*C0) + d(H_0*G_0)
  = dU * C0 + U * dC0 + dH * G_0 + H_0 * dG.
```

Therefore

```text
dY11_0 - dH * G_0 - H_0 * dG - dU * C0
  = U * dC0
  = Tail^{-1} * v.Ctop.
```

In tuple notation, the intended component theorem is

```text
((D raw z) v).Ctop
  - d(coord.F2 (0 : Fin (M+1)).succ)(v) * coord.solvedA3 0
  - coord.F2 (0 : Fin (M+1)).succ * d(coord.solvedA3 0)(v)
  - d(Tail^{-1})(v) * coord.Ctop
= Tail^{-1} * v.Ctop.
```

The matrix order is forced: `dH` and `H_0` have shape
`rho x kappa'((0 : Fin (M+1)).succ)`, `G_0` and `dG` have shape
`kappa'((0 : Fin (M+1)).succ) x rho`, and `dU`, `U`, and `Ctop` are square
`rho x rho` matrices.

## Formal Raw-Order Comparison

The transported formal raw-order Jacobian sends the raw `Ctop` tangent to

```text
Tail^{-1} * v.Ctop.
```

Thus the sheared actual derivative component above should agree with the
`Ctop` component of `retainedPassiveFormalRawOrderJacobianAt z v`.

## Guardrails

- This is the first top-left coordinate only; it complements, but does not
  subsume, the passive `A1` bridge.
- The term `d(Tail^{-1})(v) * coord.Ctop` is essential.  Dropping it leaves the
  variation of the passive top-left tail.
- This does not cover the terminal lower-left `F3` coordinate.
- This does not assemble a global determinant-one shear linear equivalence,
  determinant equality, measure pushforward, normal crossings, pole order, or
  RLCT.
- The only analytic facts used are ordinary Frechet differentiation of finite
  matrix products and the already-formalized retained-passive raw block
  formulas.

## Independent Check

`Einstein the 5th`, xhigh read-only reviewer, checked the calculation after
the VM interruption and returned PASS.  The review specifically confirmed the
full `F2` slot `coord.F2 ((0 : Fin (M+1)).succ)`, the multiplication order
`dH * G`, `H * dG`, `dU * Ctop`, and the formal target
`Tail^{-1} * v.Ctop`.
