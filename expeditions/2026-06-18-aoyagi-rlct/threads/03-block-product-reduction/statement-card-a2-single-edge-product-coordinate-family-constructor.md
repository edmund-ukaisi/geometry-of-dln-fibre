# Statement Card - A2 single-edge product-coordinate family constructor

Date: 2026-06-25.

## Claim

For a single edge, prescribed p.13 regular coordinates `u` and residual matrix
`D` determine an explicit fixed-base edge matrix

```text
[ Ctop,       -Ctop F2
  -F3 Ctop,   D + F3 Ctop F2 ],
```

where `Ctop = I + X` and `X,F2,F3` are the three block projections of `u`.
If `IsUnit Ctop.det`, the fixed-base product-difference coordinate map of the
continuous edge family realised from this matrix is

```text
Sum.elim (fun c => u c) (AoyagiResidualBlockCoordinateIndex.value D).
```

## Lean Artifacts

```text
AoyagiResidualBlockCoordinateIndex.matrix
AoyagiResidualBlockCoordinateIndex.value_matrix
AoyagiResidualBlockCoordinateIndex.exists_value_eq
paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_singleEdgeProductCoordinateEuclidean
```

## Inputs Kept Explicit

- the Euclidean regular-coordinate vector `u`;
- the residual matrix `D`;
- the determinant chart hypothesis `IsUnit (Ctop(u)).det`;
- the fixed endpoint bases from the existing fixed-base chart API.

## Nonclaims

No multi-edge product-coordinate family is constructed.  No base residual is
chosen, no residual-product preservation theorem is proved, no source
coverage or determinant-neighborhood theorem is proved, and no analytic
chart, density/Jacobian transport, normal crossings, pole order, or RLCT
extraction is proved.

## Verification

Verified in Lean.  Focused build:
`LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates`.
Full build:
`LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre`.
`scripts/sorries` reports zero `sorry`, `#exit`, `native_decide`, and `axiom`;
`git diff --check` is clean.
