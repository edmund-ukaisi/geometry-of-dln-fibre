# Statement Card - A2 fixed-base adapted endpoint Frobenius comparison

## Statement

In the fixed adapted endpoint bases attached to a base paper chain `B`, the base
endpoint total matrix is

```text
[[I, 0], [0, 0]].
```

For a real variable edge family `Cedge`, the adapted product-difference
square-sum is the fixed-basis Frobenius square

```text
trace((T(x) - T0)^T (T(x) - T0)),
```

where `T(x)` is the fixed-base endpoint total product matrix and
`T0 = [[I,0],[0,0]]`.  The matrix orientation is rows at the target endpoint
`Fin.last N` and columns at the source endpoint `0` for the reversed-edge
chain.

Consequently the existing p. 13 product-reduction lower bounds can be stated
with this fixed adapted endpoint Frobenius loss on the right-hand side.

## Lean Names

```text
matrix_trace_transpose_mul_self_eq_aoyagiCoordinateSquareSum
paperEndpointFixedBaseTotalMatrixOfReverseEdges_selfBase_eq_fromBlocks_one_zero_zero
paperEndpointFixedBaseAdaptedProductDifferenceSquareSum_eq_baseRelative_totalMatrix_squareSum
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceFrobeniusLoss
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_of_productReductionCertificate_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_selfBase_nhdsWithin_source
```

## Source

Aoyagi p. 13 adapted endpoint product-difference block and Frobenius-square
loss notation, instantiated in the fixed-base endpoint coordinates already
formalised for the product-reduction thread.

## Dependencies

- fixed-base adapted endpoint basis construction;
- base endpoint total matrix block identity;
- finite real matrix identity `trace(M^T M) = sum entries M_ij^2`;
- existing fixed-base product-reduction certificate bounds.

## Nonclaims

No original `lossDLN` comparison, no original-coordinate basis-change norm
comparison, no statistical/KL/covariance loss statement, no analytic product
chart, no source-rank openness, no density/Jacobian transport, no
regular-suspension additivity theorem, no normal crossings, no pole order, and
no RLCT extraction is proved.
