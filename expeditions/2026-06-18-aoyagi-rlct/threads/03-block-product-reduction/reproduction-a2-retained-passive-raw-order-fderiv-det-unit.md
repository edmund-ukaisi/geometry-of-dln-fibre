# Reproduction - A2 Retained-Passive Raw-Order FDeriv Determinant Unit

Date: 2026-06-26.

Status: pen-and-paper reproduction for determinant unitness of the ambient
Frechet derivative of the retained-passive raw-order chart map on the tuple
determinant chart.  This is local real-coordinate calculus only.  It does not
compute a determinant formula, a density, a measure pushforward, a
normal-crossing statement, pole order, or an RLCT consequence.

Source anchor: Aoyagi 2023 pp. 10-13, the block-elimination/product-reduction
coordinate chart behind Lemma 2 and Theorem 3.  No quiver-paper input is used.

## Setup

Let

```text
S = topologyTupleDetChartSet,
T = topologyTupleRawOrderSourceRecursiveDetChartSet,
f = topologyTupleEdgeRawOrder,
g = topologyTupleEdgeRawOrderInverse.
```

The previous retained-passive slices established:

```text
f maps S into T,
g maps T into S,
g(f(x)) = x for x in S,
f(g(y)) = y for y in T,
S and T are open,
f is differentiable at every x in S,
g is differentiable at every y in T.
```

Fix `z in S` and set `y = f(z)`.  Then `y in T`.

## Neighborhood Inverse Identities

The inverse identities are chart-set identities, but the chain rule for
ordinary `fderiv` needs identities in the ambient neighborhood filters.  Since
`S` is open and `z in S`,

```text
S in nhds(z).
```

Therefore the identity `g(f(x)) = x` for all `x in S` gives

```text
g o f = id      eventually in nhds(z).
```

Likewise, since `T` is open and `y in T`,

```text
T in nhds(y),
```

and the identity `f(g(u)) = u` for all `u in T` gives

```text
f o g = id      eventually in nhds(y).
```

This is the only place openness is used.  No within-derivative theorem is
needed because the landed differentiability facts are ambient
`DifferentiableAt` statements.

## Tangent Inverse

The chain rule at `z` gives

```text
D(g o f)_z = Dg_y * Df_z.
```

The eventual equality `g o f = id` near `z` identifies the left-hand side with

```text
D(id)_z = 1.
```

Thus

```text
Dg_y * Df_z = 1.
```

Similarly, the chain rule at `y` and the eventual equality `f o g = id` near
`y` give

```text
Df_z * Dg_y = 1,
```

using `g(y) = z`.

Hence the two continuous linear maps `Df_z` and `Dg_y` are inverse tangent
maps.  In particular the source derivative `Df_z` is a unit as a finite real
linear endomorphism.

## Determinant Unit

Taking determinants in

```text
Dg_y * Df_z = 1
```

gives

```text
det(Dg_y) * det(Df_z) = 1.
```

Therefore `det(Df_z)` is a unit in `R`.  Over `R = real`, this is equivalent
to `det(Df_z) != 0`.

The argument proves determinant unitness, not a closed determinant formula.
The actual numerical monomial/unit factor for Aoyagi's p. 13 density remains a
separate calculation.

## Nonclaims

No explicit derivative formula, determinant formula, Jacobian density, measure
pushforward, source-rank coverage, normal-crossing theorem, pole order, or
RLCT statement is proved by this slice.
