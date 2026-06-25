# Statement Card - A2 product-family assumption-reduction sockets

Date: 2026-06-25.

## Claim

The two direct socket hypotheses behind the product-coordinate adapted
lower-bound socket, plus the `F2/F3` smallness input to one composed wrapper,
can be reduced to more concrete finite-coordinate assumptions:

- the cleaned-to-literal comparison follows from supplied `F2/F3` smallness
  for `CedgeProd(x,u)`;
- the product-coordinate square-sum shape follows from supplied component
  identities for the regular and residual coordinate maps.
- when the regular-coordinate identity is literal and `Rmax <= 1`, the
  product-family `F2/F3` smallness follows from Euclidean ball membership.

## Lean Artifacts

```text
paperEndpointFixedBaseRegularBlockF2F3SquareSum

PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_of_regularBlockF2F3SquareSum_le_one

PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_eventually_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_nhdsWithin_source_prod_of_regularBlockF2F3SquareSum_le_one

PaperEndpointFixedBaseRegularCoordinateSourceData.productCoordinateShape_nhdsWithin_source_of_regular_residual_coordinateMap_eq

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_regularBlockF2F3Small_nhdsWithin_source

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularBlockF2F3Small_nhdsWithin_source

aoyagiCoordinateSquareSum_le_one_of_mem_ball_le_one

AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_add_le_coordinateSquareSum

PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_regularBlockCoordinateMap_squareSum

PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_one_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one

PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_eventually_le_one_nhdsWithin_source_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularRadius_le_one_nhdsWithin_source
```

## Inputs Kept Explicit

- product family `CedgeProd`;
- component coordinate identities for the shape bridge;
- product-family `F2/F3` smallness for the supplied-smallness bridge, or
  literal regular-coordinate equality plus `Rmax <= 1` for the radius-derived
  bridge;
- product-reduction certificates and triangular multiplier bound for the
  composed adapted lower-bound socket;
- positive regular radius and positive multiplier bound.  The finite
  radius-derived smallness lemma itself only uses `Rmax <= 1`; `0 < Rmax` is
  retained by the composed socket as a positive-radius interface/nonvacuity
  condition.
- the source-filter hypotheses are `nhdsWithin`-eventual in the base variable
  and uniform over `u` in the regular ball; they are not product-neighborhood
  or product-chart hypotheses.

## Nonclaims

No product chart, analytic coordinate construction, source coverage,
signed-box pushforward, density/Jacobian transport, normal crossings, pole
order, or RLCT extraction is proved.

The radius-derived smallness theorem requires literal coordinate equality
`regularBlock(CedgeProd(x,u)) = u`.  It does not cover a hidden permutation,
scaling, or linear coordinate change without an additional norm-comparison
bound.

## Verification

Checked with:

```text
cd lean
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```
