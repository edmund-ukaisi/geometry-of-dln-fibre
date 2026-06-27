# Reproduction - A2 Retained-Passive Raw-Order Weighted Change of Variables

Date: 2026-06-27.

Status: pen-and-paper reproduction for the first measure-transport theorem for
the retained-passive raw-order chart.  This is a direct Jacobian
change-of-variables interface for the raw-order tuple endomap, not an inverse
density theorem and not a source-density construction.

Source anchor: Aoyagi 2023 pp. 10-13, the local block-elimination/product
coordinate change used in Lemma 2 and Theorem 3.  The measure-theoretic
Jacobian theorem is the proved upstream Mathlib theorem
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar`; this slice adds the
Aoyagi retained-passive adapter to that theorem.

## Setup

Let

```text
E = TopologyTuple rho kappa' R,
S = topologyTupleDetChartSet,
T = topologyTupleRawOrderSourceRecursiveDetChartSet,
f = topologyTupleEdgeRawOrder.
```

The retained-passive topology and derivative layers already prove:

```text
S is open,
f is injective on S,
f '' S = T,
f is differentiable at every z in S.
```

The latest density interface defines

```text
Jabs(z) = |det (fderiv R f z)|.
```

## Within-Derivative Input

For a point `z in S`, ambient differentiability gives

```text
HasFDerivAt f (fderiv R f z) z.
```

Restricting the domain from the whole ambient tuple space to `S` gives

```text
HasFDerivWithinAt f (fderiv R f z) S z.
```

This is the derivative hypothesis needed by the Mathlib Jacobian theorem.
No continuity of `z |-> fderiv R f z` is needed.

## Weighted Pushforward

Let `m` be an additive Haar measure on `E`, and assume `S` is
`m`-null-measurable.  Since `S` is open and the tuple space is Borel, this
null-measurability follows automatically in the usual Borel setting.

Mathlib's set-level Jacobian theorem says that for an injective map
differentiable within `S`,

```text
map f ((m.restrict S).withDensity (fun z => ofReal |det Df_z|))
  = m.restrict (f '' S).
```

Substituting `Jabs(z)` for `|det Df_z|` gives

```text
map f ((m.restrict S).withDensity (fun z => ofReal (Jabs z)))
  = m.restrict (f '' S).
```

Using the retained-passive image theorem `f '' S = T`, the target can also be
rewritten as

```text
m.restrict T.
```

## Boundary

This slice proves only the forward weighted change-of-variables identity on
the retained-passive raw-order determinant chart.  It does not prove an
explicit determinant formula, continuity of the determinant density, local
bounded-density estimates, an inverse Jacobian density, a source-prior density
identity, the original DLN source pushforward, normal crossings, pole order, or
RLCT.
