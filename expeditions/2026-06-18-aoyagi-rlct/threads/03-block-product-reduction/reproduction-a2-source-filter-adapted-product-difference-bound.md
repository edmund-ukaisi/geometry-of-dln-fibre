# Reproduction - A2 source-filter adapted product-difference bound

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the source-filter
lift of the fixed-base adapted product-difference bound.

## Source Anchor

This is still the p. 13 triangular block display, but now used on the
source-rank `nhdsWithin` filter.  The source filter is

```text
nhdsWithin x0 (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge).
```

The product-reduction certificate and multiplier square-sum bound are supplied
eventually on that filter.

## Derivation

The pointwise theorem gives, for each `x`,

```text
c * literalSquareSum(x) <= adaptedProductDifferenceSquareSum(x)
```

provided `x` has the fixed-base product-reduction certificate and

```text
triangularMultiplierSquareSumProduct(x) <= Kmul,
c >= 0,
c*Kmul <= 1.
```

If the certificate and multiplier bound hold eventually on the source-rank
filter, then filtering upward gives the same inequality eventually.

Combining this eventual literal lower bound with the already-proved finite
p. 13 comparison

```text
(1/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= literalSquareSum(x)
```

gives

```text
(c/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= adaptedProductDifferenceSquareSum(x)
```

eventually on the same source-rank filter.

## Lean Shape

Lean proves the source-filter literal bound and the cleaned regular/residual
consequence in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

with names

```text
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceSquareSum_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productReductionCertificate_nhdsWithin_source
```

## Boundary

The right-hand side is still only the adapted fixed-base product-difference
square-sum.  This is not `lossDLN` and not the original statistical loss.  The
theorems do not prove local multiplier boundedness, source-rank openness,
covariance lower bounds, basis norm equivalence, analytic chart construction,
Jacobian/prior transport, regular-suspension Fubini/polar shift, normal
crossings, pole order, or RLCT extraction.
