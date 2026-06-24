# Statement Card - A2 fixed-base literal-cleaned square-sum comparison

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
PaperEndpointFixedBaseRegularCoordinateSourceData.literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two
PaperEndpointFixedBaseRegularCoordinateSourceData.literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.literalProductDifferenceCoordinateMap_squareSum_eventually_le_two_mul_productDifferenceCoordinateMap_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum
PaperEndpointFixedBaseRegularCoordinateSourceData.literalProductDifferenceCoordinateMap_squareSum_eventually_le_two_mul_productDifferenceCoordinateMap_squareSum_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_nhdsWithin_source
```

## Statement Shape

For real fixed-base regular-coordinate source data, eventually in `nhds x0`
the actual literal signed/corrected coordinate square-sum and the actual
cleaned product-difference coordinate square-sum are mutually bounded by
factor `2`.

The source-rank-stratum variants state the same inequalities in

```text
nhdsWithin x0 (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge).
```

The directional theorems expose each inequality separately; the conjunction
theorems package the two inequalities together.

## Proof Inputs

- Fixed-base smallness:
  `regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one`.
- Finite comparison:
  `AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one`.
- Reverse finite comparison:
  `AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one`.

## Scope

Finite real square-sum comparison for the fixed-base scalar coordinate maps.

## Nonclaims

No analytic ideal transport, no analytic chart construction, no source
coverage, no source-rank openness, no normal-crossing construction, no pole
order, and no RLCT extraction.
