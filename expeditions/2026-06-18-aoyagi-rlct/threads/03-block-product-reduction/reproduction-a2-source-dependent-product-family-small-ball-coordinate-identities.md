# Reproduction - A2 source-dependent product family small-ball coordinate identities

Date: 2026-06-25.

Status: pen-and-paper reproduction for the small regular-coordinate ball on
which the source-dependent p.13 product family has the intended coordinate
readout.

## Source Boundary

This slice starts from the already-proved pointwise theorem for the
source-dependent multi-edge product-coordinate family.  It only removes the
pointwise determinant-unit hypothesis by shrinking the Euclidean regular
coordinate radius.  It does not prove a product chart, source coverage,
measure transport, normal crossings, pole order, or RLCT extraction.

## Calculation

For a base source family `CedgeBase`, the product family is

```text
CedgeProd(x,u) =
  paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
    CedgeBase (x,u).
```

The pointwise readout theorem says that if

```text
IsUnit(det(Ctop(u))),
```

then

```text
regular(CedgeProd(x,u)) = u,
residual(CedgeProd(x,u)) = residual(CedgeBase x).
```

Here `Ctop(u) = I + X(u)`, where `X(u)` is the first regular-coordinate
matrix block decoded from the Euclidean vector `u`.  At `u = 0`,

```text
Ctop(0) = I,
det(Ctop(0)) = 1,
```

so `det(Ctop(0))` is a unit over `R`.  Since matrix assembly and determinant
are continuous in finite coordinates, `IsUnit(det(Ctop(u)))` holds on some
Euclidean ball around `0`.  Given any prescribed positive `Rmax`, shrink this
ball to a radius `R` with

```text
0 < R,     R <= Rmax,
```

and the determinant-unit hypothesis holds for every `u` in `ball(0,R)`.

Substituting this into the pointwise readout theorem gives, for every source
point `x` and every `u` in the smaller ball,

```text
regular(CedgeProd(x,u)) = u,
residual(CedgeProd(x,u)) = residual(CedgeBase x).
```

Because the assertion is pointwise in `x`, it is automatically eventual along
any source filter, in particular

```text
nhdsWithin x0 (paperEndpointFixedBaseSourceRankStratum CedgeBase r rEdge).
```

## Lean Target

The determinant-small-ball input already exists as

```text
AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
```

and the pointwise readout input is

```text
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
```

The target theorem packages these as a radius plus two eventual identities:

```text
exists_pos_radius_le_regular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily_nhdsWithin_source
```

## Boundary

The theorem is multi-edge (`N = M + 2`) and only concerns finite-coordinate
readout of the constructed p.13 product family on a small regular-coordinate
ball.  It leaves product-reduction certificates, triangular multiplier bounds,
chart coverage, source measure, normal crossings, and RLCT to separate slices.
