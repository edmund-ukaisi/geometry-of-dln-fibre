# Statement Card - A2 fixed-base product-coordinate edge matrices

Date: 2026-06-25.

## Claim

The p.13 raw product-coordinate edge matrix patterns now feed the fixed-base
product-difference coordinate readout.

For a chain with at least two edges, if the fixed-base edge matrices satisfy

```text
right endpoint: [I, 0; -F3, C_last],
middle edges:   [I, 0; 0, C_p],
left endpoint:  [Ctop, -Ctop F2; 0, C_0],
```

and `IsUnit Ctop.det`, then the cleaned fixed-base coordinate map is

```text
value(Ctop - I, F2, F3, residualProduct EMat last 0).
```

For a single edge, the raw matrix

```text
[Ctop, -Ctop F2; -F3 Ctop, C0 + F3 Ctop F2]
```

gives coordinate readout

```text
value(Ctop - I, F2, F3, C0).
```

## Lean Artifacts

```text
ChartLocalSuffixState.productCoordinateRightEndpointMatrix
ChartLocalSuffixState.productCoordinateMiddleMatrix
ChartLocalSuffixState.productCoordinateLeftEndpointMatrix
ChartLocalSuffixState.productCoordinateSingleEdgeMatrix
ChartLocalSuffixState.suffixState_tail_fields_of_productCoordinateEdges
ChartLocalSuffixState.suffixState_productCoordinate_fields_one
ChartLocalSuffixState.suffixState_productCoordinate_fields_succSucc
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdgeMatrix_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdges_succSucc
```

## Inputs Kept Explicit

- raw fixed-base edge matrix shapes;
- `IsUnit Ctop.det`;
- fixed endpoint bases from `paperEndpointFixedBaseEdgeMatrixOfReverseEdges`;
- residual product from the suffix recursion in the multi-edge case.

## Nonclaims

No dependent product-family constructor `G(x,u)` is built.  No
parameter-continuity, source coverage, signed-box pushforward, density/Jacobian
transport, analytic regular-suspension chart, normal crossings, pole order, or
RLCT extraction is proved.

## Verification

Checked with:

```text
cd lean
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```
