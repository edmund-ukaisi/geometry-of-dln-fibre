# Statement Card - A2 multi-edge source-dependent product-coordinate family

Date: 2026-06-25.

## Claim

For a chain with at least two edges, a base source edge family `CedgeBase`, a
source point `x`, and a Euclidean regular-coordinate vector `u` determine a
pointwise product-coordinate edge family `CedgeProd`.  If
`IsUnit(det(Ctop(u)))`, then at `(x,u)`:

```text
regularBlockCoordinateMap(CedgeProd) = u
residualBlockCoordinateMap(CedgeProd) =
  residualBlockCoordinateMap(CedgeBase x).
```

## Lean Artifacts

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
```

## Inputs Kept Explicit

- the base source edge family `CedgeBase`;
- the point `x`;
- the Euclidean regular-coordinate vector `u`;
- the determinant chart hypothesis `IsUnit (Ctop(u)).det`;
- the fixed-base chart data `U₀` and `hU₀`.

## Nonclaims

No continuity in `(x,u)` is proved.  No determinant-neighborhood theorem,
source coverage, product chart, signed-box pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT extraction is proved.

## Verification

Focused build passed:
`LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates`.
Full build passed:
`LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre`.
`scripts/sorries` reports zero `sorry`, `#exit`, `native_decide`, and `axiom`;
`git diff --check` is clean.
