# Statement Card - A2 fixed-base product-family coordinate readout

Date: 2026-06-25.

## Claim

For a fixed-base chain with at least two edges, the matrix-level
product-family suffix-field theorem now feeds the fixed-base p.13
product-difference coordinate map.

If the fixed-base edge matrices satisfy the transformed-edge shapes

```text
right endpoint: [I, 0; -F3, C_last],
middle edges:   [I, 0; 0, C_p],
left endpoint:  [Ctop, -Ctop F2; 0, C_0],
```

with `IsUnit Ctop.det`, then the cleaned fixed-base product-difference
coordinate map is exactly

```text
value(Ctop - I, F2, F3, residualProduct EMat last 0).
```

The residual block is the product of the transformed Schur residual factors,
not an arbitrary supplied final matrix.

## Lean Artifacts

```text
paperEndpointFixedBaseRegularBlockCoordinateMap_eq_of_suffixState_fields
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_of_suffixState_D
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdges_succSucc
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdges_succSucc
```

## Inputs Kept Explicit

- the fixed endpoint bases are those from `paperEndpointFixedBaseEdgeMatrixOfReverseEdges`;
- transformed-edge block-shape hypotheses are supplied;
- `IsUnit Ctop.det` is supplied;
- the residual coordinate is `residualProduct EMat last 0`;
- the theorem is only for the `succSucc` case, i.e. at least two edges.

## Nonclaims

No concrete product-family `CedgeProd` is constructed.  No theorem proves that
fixed-base continuous linear maps realize the transformed-edge hypotheses.  No
source coverage, signed-box pushforward, density/Jacobian transport, analytic
regular-suspension chart, normal crossings, pole order, or RLCT extraction is
proved.

## Verification

Checked with:

```text
cd lean
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```
