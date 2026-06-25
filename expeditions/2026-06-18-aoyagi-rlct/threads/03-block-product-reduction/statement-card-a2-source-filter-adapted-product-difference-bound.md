# Statement Card - A2 source-filter adapted product-difference bound

## Statement

On the fixed-base source-rank `nhdsWithin` filter, if both the
product-reduction certificate and the triangular multiplier square-sum bound
hold eventually, then

```text
c * literalSquareSum(x) <= adaptedProductDifferenceSquareSum(x)
```

holds eventually for every `c >= 0` with `c*Kmul <= 1`.

With fixed-base regular-coordinate source data, the cleaned consequence is

```text
(c/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= adaptedProductDifferenceSquareSum(x)
```

eventually on the same filter.

## Lean Names

```text
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceSquareSum_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productReductionCertificate_nhdsWithin_source
```

## Source

Aoyagi p. 13 triangular display, plus the existing fixed-base
product-reduction certificate and finite literal/cleaned p. 13 comparison.

## Dependencies

- pointwise fixed-base adapted product-difference certificate bound;
- eventual product-reduction certificate on the source-rank filter;
- eventual triangular multiplier square-sum bound;
- fixed-base regular-coordinate source data for the cleaned consequence.

## Nonclaims

No original DLN loss comparison, covariance lower bound, basis norm
equivalence, local multiplier boundedness theorem, source-rank openness,
analytic chart construction, Jacobian/prior transport, regular-suspension
theorem, normal crossings, pole order, or RLCT extraction is proved.
