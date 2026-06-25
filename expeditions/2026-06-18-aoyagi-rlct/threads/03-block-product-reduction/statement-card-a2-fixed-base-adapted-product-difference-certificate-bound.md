# Statement Card - A2 fixed-base adapted product-difference certificate bound

## Statement

For a fixed-base product-reduction certificate at a point `x`, if the
deterministic p. 13 triangular multiplier square-sum product is at most
`Kmul`, then every `c >= 0` with `c*Kmul <= 1` satisfies

```text
c * squareSum(literal p.13 coordinates at x)
  <= adaptedProductDifferenceSquareSum(x).
```

The right-hand side is the square-sum of the fixed-base endpoint total product
matrix minus `[I,0;0,0]`.

## Lean Names

```text
paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceSquareSum
```

## Source

Aoyagi p. 13 triangular block display, instantiated through the existing
fixed-base product-reduction certificate.

## Dependencies

- `PaperEndpointFixedBaseProductReductionCertificate.blockDiagonal`;
- `ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular`;
- the finite p. 13 triangular-multiplier square-sum comparison;
- a supplied pointwise multiplier square-sum bound.

## Nonclaims

No original DLN loss comparison, covariance lower bound, basis norm
equivalence, local multiplier boundedness theorem, source-rank openness,
analytic chart construction, Jacobian/prior transport, regular-suspension
theorem, normal crossings, pole order, or RLCT extraction is proved.
