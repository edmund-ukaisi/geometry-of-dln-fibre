# Reproduction - A2 retained-passive actual derivative passive A1 shear bridge

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; independent xhigh check passed;
Lean target implemented.

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
data  = ofTopologyTuple z
coord = data.toCoordinateData.
```

For a passive top-left coordinate `p : Fin M`, set

```text
q   = p.succ : Fin (M+1),
A_q = coord.solvedA1 q,
H_q = coord.F2 q.succ,
G_q = coord.solvedA3 q.
```

The index `q` is nonzero.  Therefore the solved top-left family does not use
the first-edge solve:

```text
A_q = coord.A1seed q = data.A1passive p.
```

Consequently, for a tangent vector `v`,

```text
dA_q(v) = v.A1passive p.
```

The successor `H_q = coord.F2 q.succ` uses the full `F2full` endpoint
convention.  If `q` is the last edge, then `q.succ` is the terminal
`Fin (M+2)` index and `H_q = 0`.

## Raw Formula

The raw top-left block for edge `q : Fin (M+1)` is

```text
Y11_q = A_q + H_q * G_q.
```

For the stored passive top-left coordinate `p`, the target tuple component is
the raw top-left edge `q = p.succ`:

```text
(raw z).A1passive p = Y11_(p.succ).
```

## Calculation

Differentiate the raw top-left block:

```text
dY11_q
  = dA_q + dH_q * G_q + H_q * dG_q.
```

Therefore

```text
dY11_q - dH_q * G_q - H_q * dG_q
  = dA_q
  = v.A1passive p.
```

In tuple notation, the desired component theorem is

```text
((D raw z) v).A1passive p
  - d(coord.F2 p.succ.succ)(v) * coord.solvedA3 p.succ
  - coord.F2 p.succ.succ * d(coord.solvedA3 p.succ)(v)
= v.A1passive p.
```

The matrix order is forced: `dH_q` and `H_q` have shape
`rho x kappa'(q.succ)`, while `G_q` and `dG_q` have shape
`kappa'(q.succ) x rho`.

## Terminal Passive Edge

When `p` is the last passive top-left coordinate, `q = p.succ` is the last
edge of `Fin (M+1)`.  Then

```text
H_q = coord.F2 q.succ = 0,
dH_q = 0.
```

The same formula specializes to

```text
dY11_q = dA_q = v.A1passive p.
```

No separate terminal theorem is mathematically needed if the statement keeps
the full `F2full` convention.

## Formal Raw-Order Comparison

The transported formal raw-order Jacobian has apply formula

```text
(A1passive, F2, A3passive, C, Ctop, F3)
  |-> (A1passive, ..., A3passive, ..., ..., ...).
```

Thus its passive top-left component is unchanged:

```text
(retainedPassiveFormalRawOrderJacobianAt z v).A1passive p
  = v.A1passive p.
```

Combining this with the sheared actual derivative identity gives the passive
`A1` component bridge to the point-specialized formal raw-order map.

## Guardrails

- This does not cover the first top-left coordinate `Ctop`.  That coordinate
  involves the solved first-edge top-left block
  `coord.solvedA1 0 = tail^{-1} * coord.Ctop` and requires tail-product
  derivative corrections.
- This does not cover the terminal lower-left `F3` coordinate.
- This does not assemble a global determinant-one shear linear equivalence,
  determinant equality, measure pushforward, normal crossings, pole order, or
  RLCT.
- The only analytic facts used are ordinary Frechet differentiation of finite
  matrix products and the already-formalized retained-passive raw block
  formulas.
