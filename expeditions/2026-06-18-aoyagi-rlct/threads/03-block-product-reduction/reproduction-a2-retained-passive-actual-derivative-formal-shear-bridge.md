# A2 Retained-Passive Actual Derivative To Formal Shear Bridge

Status: controller reproduction; first Lean target selected.

## Scope

This note records the next analytic comparison layer for the
retained-passive raw-order map

```text
topologyTupleEdgeRawOrder :
  TopologyTuple rho kappa' R -> TopologyTuple rho kappa' R.
```

The already-landed formal raw-order determinant theorem is a finite linear
algebra calculation.  It is not yet the determinant of the actual Frechet
derivative.  The missing bridge is to factor the actual derivative into
determinant-one target shears and the formal determinant-bearing diagonal
pieces.

## Raw Edge Formulas

At a source tuple `z`, write

```text
data  = ofTopologyTuple z
coord = data.toCoordinateData
A p   = coord.solvedA1 p
G p   = coord.solvedA3 p
F i   = coord.F2 i
C p   = coord.C p.
```

For each edge `p : Fin (M+1)`, the raw target blocks are

```text
Y11_p = A p + F(p.succ) * G p
Y12_p = - A p * F(p.castSucc)
        + F(p.succ) * (C p - G p * F(p.castSucc))
Y21_p = G p
Y22_p = C p - G p * F(p.castSucc).
```

Lean stores the `Y22_p` family as the target `C` coordinate and the `Y21_p`
family in the raw lower-left readout `rawEdgeTupleA3`.

## Differential Check

For a tangent vector `v`, abbreviate actual differentials by

```text
dA_p = d(solvedA1 p)(v)
dG_p = d(solvedA3 p)(v)
dF_i = v.F2_i
dC_p = v.C_p.
```

Differentiating the lower-right raw block gives

```text
dY22_p = dC_p - dG_p * F(p.castSucc) - G p * dF_(p.castSucc).
```

The lower-left raw block is

```text
Y21_p = G p,
```

so

```text
dY21_p = dG_p.
```

Consequently the target shear

```text
(Y21_p, Y22_p) |-> (Y21_p, Y22_p + Y21_p * F(p.castSucc))
```

has derivative-level effect

```text
dY22_p + dY21_p * F(p.castSucc)
  = dC_p - G p * dF_(p.castSucc).
```

This is exactly the `C` component of the formal raw-order map after the
target shear:

```text
v.C_p - coord.solvedA3 p * v.F2_p.
```

The shear uses the basepoint matrix `F(p.castSucc)` as a fixed coefficient.
As a target-coordinate linear map, it is triangular with identity diagonal, so
it has determinant one.  This note does not yet assemble the global
determinant factorization.

## First Lean Target

The bounded theorem is the component identity

```lean
fderiv_topologyTupleEdgeRawOrder_C_unshear_apply
```

with shape

```text
((fderiv R raw z) v).C p
  + rawEdgeTupleA3 ((fderiv R raw z) v) p * coord.F2 p.castSucc
= v.C p - coord.solvedA3 p * v.F2 p.
```

This proves a real analytic derivative statement about the actual Frechet
derivative of `topologyTupleEdgeRawOrder`.  It is not a wrapper around the
formal determinant theorem.

The matching point-specialized formal-map corollary is

```lean
C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

It rewrites the right side through `retainedPassiveFormalRawOrderJacobianAt`
and `retainedPassiveFormalRawOrderJacobian_apply`, proving only the sheared
`C` component agreement with the formal raw-order map.

## Guardrails

- Do not infer the full equality
  `topologyTupleEdgeRawOrderFDerivAbsDet =
   retainedPassiveFormalRawOrderJacobianAbsDetAt` from this component.
- Do not identify `Tail` with `LastTop`; the endpoint solve for `F3` is a
  separate determinant-bearing factor.
- Do not cite normal-crossing-to-RLCT extraction here.  This is elementary
  coordinate calculus inside Aoyagi's p.13 chart.
- The source-fidelity claim remains local: the formulas above are the
  retained-passive p.13 raw-block formulas already formalised in Lean.
