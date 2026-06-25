# Statement Card - A2 product-family certificate and adapted lower bound

Date: 2026-06-25.

## Claim

For a multi-edge chain and a self-based source family `CedgeBase`, the explicit
source-dependent p.13 product-coordinate family admits a small regular-
coordinate radius `R` and a positive constant `c` such that, eventually on the
base source-rank stratum and uniformly for `u in ball(0,R)`,

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

## Inputs Kept Explicit

- multi-edge shape `N = M + 2`;
- fixed-base data `U0, hU0`;
- base-family continuity at `x0`;
- self-base equality `CedgeBase x0 = reverseEdge B`;
- source-rank parameters `r, rEdge`;
- a positive outer regular-coordinate radius `Rmax`.

## Nonclaims

No source coverage, product chart, original-loss comparison, measure
pushforward, density/Jacobian transport, normal-crossing certificate, pole
order, or RLCT extraction is proved.

## Verification

Focused build passed:
`env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates`.
