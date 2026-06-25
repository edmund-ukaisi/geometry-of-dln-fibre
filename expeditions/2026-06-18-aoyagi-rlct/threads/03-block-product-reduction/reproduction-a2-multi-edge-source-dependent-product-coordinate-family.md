# Reproduction - A2 multi-edge source-dependent product-coordinate family

Date: 2026-06-25.

Status: pen-and-paper reproduction for the pointwise source-dependent
multi-edge p.13 product-coordinate family.

## Source Boundary

This extends the fixed-`Ebase` constructor by taking `Ebase` to be the
fixed-base edge matrices of an existing base source family `CedgeBase x`.
The result is pointwise in `(x,u)`: it proves component coordinate identities
for the constructed product family at that point.

It does not prove continuity in `(x,u)`, construct a product chart, prove
source coverage, prove a determinant-neighborhood theorem for `Ctop(u)`,
transport density/Jacobian factors, produce normal crossings, prove pole
order, or extract RLCT.

## Calculation

For a source point `x`, define the base fixed-coordinate edge matrices

```text
Ebase(x)_p =
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges(CedgeBase x)_p.
```

For a Euclidean regular-coordinate vector `u`, decode

```text
X(u), F2(u), F3(u),   Ctop(u) = I + X(u).
```

For each edge `p`, choose the product-coordinate residual factor

```text
C_p(x) = residualBlock(Ebase(x), last, p).
```

Then assemble the raw p.13 matrices:

```text
G_last(x,u) = [ I  0 ; -F3(u)  C_last(x) ],
G_p(x,u)    = [ I  0 ; 0       C_p(x)    ]     for middle edges,
G_0(x,u)    = [ Ctop(u)  -Ctop(u)F2(u) ; 0  C_0(x) ].
```

Let `CedgeProd(x,u)` be the continuous fixed-base edge family realised from
these matrices.  The fixed-`Ebase` theorem gives

```text
regular(CedgeProd(x,u)) = u
residual(CedgeProd(x,u)) = value(residualProduct(Ebase(x), last, 0)).
```

The base residual-coordinate map itself is the scalar readout of the same
deterministic suffix residual product:

```text
residual(CedgeBase x) = value(residualProduct(Ebase(x), last, 0)).
```

Thus

```text
regular(CedgeProd(x,u)) = u,
residual(CedgeProd(x,u)) = residual(CedgeBase x).
```

The only chart hypothesis used by the product-coordinate readout is

```text
IsUnit(det(Ctop(u))).
```

No determinant or rank hypothesis is added to `Ebase(x)`.

## Lean Target

The new fixed-base residual readout and pointwise congruence helpers are:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
```

The source-dependent family and component theorem are:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
```

The theorem is intentionally pointwise.  A downstream eventual statement over
`x` and `u` needs either an explicit `hCtop` hypothesis at each point or a
separate small-neighborhood theorem proving `IsUnit(det(Ctop(u)))`.

## Boundary

This is finite coordinate algebra for chains with at least two edges.  It
does not cover the one-edge endpoint-collapse case, parameter-continuity,
chart/source coverage, density/Jacobian transport, normal crossings, pole
order, or RLCT extraction.
