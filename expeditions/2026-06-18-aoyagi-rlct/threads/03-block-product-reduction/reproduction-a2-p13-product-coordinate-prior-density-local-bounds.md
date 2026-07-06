# A2 p.13 Product-Coordinate Prior-Density Local Bounds

## Source Calculation

Aoyagi's Definition 1 uses an a priori density `phi(w)` in the local zeta
integral.  In the DLN main theorem setup on p.8, the prior density is assumed
to be `C^\infty`, compactly supported, and positive at the true parameter
`w*`.  The p.13 product-coordinate calculation rewrites the local product
difference using retained passive source variables plus regular variables
`(Ctop - I, F2, F3)`.

Fix the explicit Lean p.13 product-coordinate edge-family map

```text
CedgeProd : alpha x EuclideanSpace R Coord -> EdgeFamily.
```

The previous checkpoint proved that if `CedgeProd` is the self-base p.13
product-coordinate map and `phi` is continuous and positive at
`CedgeProd (x0, 0)`, then

```text
Phi(z) = phi(CedgeProd z)
```

is continuous and positive at `(x0,0)`.

Let `Rmax > 0`.  Since `Phi` is continuous at `(x0,0)` and `Phi(x0,0) > 0`,
the interval

```text
(0, Phi(x0,0) + 1)
```

is a neighborhood of `Phi(x0,0)`.  Its preimage under `Phi` is a product
neighborhood of `(x0,0)`.  Therefore there are a neighborhood `Ux` of `x0` and
a ball `B(0,R0)` in the regular coordinates such that

```text
0 < Phi(x,u) < Phi(x0,0) + 1
```

for `x in Ux` and `u in B(0,R0)`.  Taking

```text
R = min R0 Rmax,
C = Phi(x0,0) + 1
```

gives `0 < R`, `R <= Rmax`, `0 <= C`, and eventually along any relative
neighborhood `nhdsWithin x0 source`,

```text
0 <= phi(CedgeProd (x,u)),
phi(CedgeProd (x,u)) <= C
```

for all `u in B(0,R)`.

## Boundary

This is only a local bounded-density consequence of continuity and positivity
after composition with the explicit p.13 product-coordinate map.  It does not
prove a change-of-variables formula, original-prior pushforward or pullback
identity, local source-image equality, source coverage, determinant/raw Haar
transport, normal crossings, pole order, or RLCT.

## Kill Conditions

- Kill or weaken the statement if the product-coordinate map is not the
  already-proved continuous self-base map.
- Kill any downstream use that treats these local pointwise bounds as a measure
  transport theorem.
- Kill any claim that compact support is needed here; the local boundedness
  uses only continuity and positivity at the base point.
