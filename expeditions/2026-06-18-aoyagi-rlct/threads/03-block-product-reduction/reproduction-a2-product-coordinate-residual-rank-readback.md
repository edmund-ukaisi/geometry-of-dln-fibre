# Reproduction - A2 product-coordinate residual-rank readback

Date: 2026-06-26.

## Scope

This slice is the reverse rank calculation for the explicit p.13
product-coordinate edge family.  It does not prove that the product-coordinate
family covers the source-rank stratum.  It only says that if a constructed
product-coordinate point is already in the source-rank stratum, then the
residual blocks used to construct it have the corresponding reduced ranks.

## Pen-And-Paper Calculation

Let the regular corner have size `r`, and let `C_j` be the transformed Schur
residual block for the base edge family at edge `j`.  The explicit p.13
product-coordinate edge matrices have three forms:

```text
[ I   0  ],       [ I   0 ],       [ Ctop   -Ctop F2 ],
[-F3  Cj ]        [ 0   Cj]        [ 0       Cj      ].
```

The right endpoint has rank `r + rank(C_j)` because multiplication by
`[I 0; F3 I]` reduces it to `[I 0; 0 C_j]`.  A middle edge is already
block-diagonal, so it also has rank `r + rank(C_j)`.  The left endpoint has
rank `r + rank(C_j)` after multiplying on the right by `[I F2; 0 I]`; here
we need `det(Ctop)` to be a unit so that `rank(Ctop)=r`.

Now assume the constructed product-coordinate point `(x,u)` lies in

```text
paperEndpointFixedBaseSourceRankStratum ... CedgeProd r rEdge.
```

The edge-rank field of this source-rank stratum gives

```text
rank(productCoordinateEdge_j(x,u)) = rEdge_j.
```

The base-product-rank field, together with the fixed basepoint certificate,
identifies the regular corner size as `r`.  Combining this with the block-rank
calculation gives

```text
r + rank(C_j) = rEdge_j.
```

Therefore

```text
rank(C_j) = rEdge_j - r.
```

The source-rank stratum also records `r <= rEdge_j`, but the displayed
equality already forces the subtraction in the intended direction.

## Lean Target

Add a pointwise theorem in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_residualBlock_rank_of_mem_sourceRankStratum
```

The theorem should consume:

- the fixed basepoint chart data `U₀`, `hU₀`;
- the base edge family `CedgeBase`;
- the source point `x` and regular coordinate `u`;
- source-rank membership for the constructed family at `(x,u)`;
- `IsUnit(det(Ctop(u)))`.

It should conclude for every edge `p`:

```text
rank(residualBlock(baseEdgeMatrix x, p)) = rEdge p - r.
```

## Boundary

Proved: finite rank readback from constructed product-coordinate source-rank
membership to the base residual block ranks.

Assumed: membership of `(x,u)` in the source-rank stratum for the constructed
family, and the left-endpoint determinant unit hypothesis.

Cited: none.

Deferred: source coverage, local inverse, source/image equality, exact-rank
openness, source-measure transport, density/Jacobian identity,
normal-crossing construction, pole order, and RLCT.

Nonclaims: no quiver input, no local source theorem, no chart construction,
and no proof that an arbitrary source-rank point is represented by the p.13
product-coordinate family.
