# Statement Card - A2 multi-edge product-coordinate family constructor

Date: 2026-06-25.

## Claim

For a chain with at least two edges, a fixed base edge-matrix family `Ebase`
and a Euclidean regular-coordinate vector `u` determine an explicit raw p.13
fixed-base edge matrix family.  Its regular coordinates are exactly `u`, and
its residual coordinates are the base residual product
`residualProduct Ebase last 0`.

The theorem requires the determinant chart hypothesis
`IsUnit (Ctop(u)).det` for the cleaned coordinate readout.

## Lean Artifacts

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_multiEdgeProductCoordinateEuclidean
```

It also consumes:

```text
ChartLocalSuffixState.suffixState_productCoordinate_fields_succSucc
ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_base
AoyagiProductDifferenceCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices_residual
```

## Inputs Kept Explicit

- the fixed base matrix family `Ebase`;
- the Euclidean regular-coordinate vector `u`;
- the determinant chart hypothesis `IsUnit (Ctop(u)).det`;
- the fixed endpoint bases and fixed-base matrix-realisation API.

## Nonclaims

No dependent source family `G(x,u)` is constructed.  No parameter-continuity,
source coverage, product chart, signed-box pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT extraction is proved.

## Verification

Focused build passed:
`LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates`.
Full build passed:
`LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre`.
`scripts/sorries` reports zero `sorry`, `#exit`, `native_decide`, and `axiom`;
`git diff --check` is clean.
