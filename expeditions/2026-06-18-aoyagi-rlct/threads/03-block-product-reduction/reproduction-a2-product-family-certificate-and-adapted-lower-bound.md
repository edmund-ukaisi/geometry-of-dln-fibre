# Reproduction - A2 product-family certificate and adapted lower bound

Date: 2026-06-25.

Status: pen-and-paper reproduction for the finite p.13 product-reduction
certificate and adapted square-sum lower bound for the explicit source-
dependent multi-edge product family.

## Source Boundary

This slice concerns only the constructed p.13 product-coordinate edge family
for chains with at least two edges.  It proves determinant-chart/certificate
and finite square-sum lower-bound facts for the adapted fixed-base product
difference.  It does not prove source coverage, measure transport, density or
Jacobian formulas, normal crossings, pole order, or RLCT extraction.

## Certificate Calculation

At a source point `x`, let `Ebase(x)` be the fixed-base matrix family of the
base edge family `CedgeBase x`.  Decode a Euclidean regular vector `u` into

```text
F2(u), F3(u), Ctop(u) = I + X(u).
```

Set the residual factors

```text
C_p(x) = residualBlock(Ebase(x), last, p).
```

The explicit product-coordinate matrices are

```text
G_last = [ I  0 ; -F3  C_last ],
G_p    = [ I  0 ;  0   C_p    ]       for middle edges,
G_0    = [ Ctop  -Ctop F2 ; 0  C_0 ].
```

After the right endpoint and middle edges, the suffix recursion has

```text
B = 0,     Ctop = I,     L = [ I 0 ; F3 I ].
```

Thus the transformed right and middle edges have identity top-left block, and
the transformed left edge has top-left block `Ctop(u)`.  Therefore all
recursive determinant charts hold as soon as

```text
IsUnit(det(Ctop(u))).
```

The existing certificate constructor turns these recursive determinant charts
into the fixed-base product-reduction certificate.  Its residual-rank clauses
remain conditional implications from exact edge ranks; no rank stratum is
claimed open.

## Multiplier Bound

The p.13 adapted lower bound uses the triangular multipliers

```text
Lmul = [ I 0 ; lowerLeft(L) I ],
Rmul = [ I -B ; 0 I ].
```

For any continuous edge family satisfying the recursive determinant charts at
a base point, the coefficient fields `-B` and `lowerLeft(L)` are continuous
there.  Hence the finite product of their multiplier square-sums is locally
bounded above by a positive constant.

For the explicit source-dependent product family, continuity at `(x0,0)` is
available in the self-base case

```text
CedgeBase x0 = reverseEdge B.
```

The pointwise certificate at `(x0,0)` supplies the recursive determinant
charts.  A product-neighborhood basis then shrinks the resulting neighborhood
to

```text
x in a neighborhood of x0,
u in ball(0,R).
```

Restricting from `nhds x0` to `nhdsWithin` the source stratum gives the
source-filter multiplier bound.

## Adapted Lower Bound

Choose a common radius by nesting the previous shrinkages:

```text
R <= Rcoord <= min(Rmax, 1),
R <= Rcert,
R <= Rmult.
```

On `ball(0,R)`:

- regular coordinates of `CedgeProd(x,u)` are exactly `u`;
- residual coordinates are the base residual coordinates of `CedgeBase x`;
- the product-reduction certificate holds for `CedgeProd(x,u)`;
- the triangular multiplier square-sum product is bounded by `Kmul`;
- the radius bound `R <= 1` gives the finite `F2/F3` smallness needed by the
  existing lower-bound socket.

The existing socket then gives a positive constant `c` such that eventually on
the base source stratum and uniformly for `u in ball(0,R)`,

```text
c * (squareSum(residual(CedgeBase x)) + squareSum(u))
  <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

## Lean Artifacts

```text
ChartLocalSuffixState.recursiveDetCharts_productCoordinateEdges_succSucc
paperEndpointFixedBaseProductReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
exists_pos_radius_le_productReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_nhdsWithin_source
exists_pos_ball_eventually_forall_mem_of_mem_nhds_prod_zero
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_of_recursiveDetCharts
exists_pos_radius_le_pos_const_triangularMultiplierSquareSumProduct_eventually_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
```

## Boundary

This is still an adapted fixed-base product-coordinate lower bound.  It does
not identify this adapted square-sum with the original DLN/statistical loss,
does not construct a product chart or source-covering map, does not transport
Lebesgue density or Jacobian factors, and does not produce normal crossings,
pole order, or RLCT.
