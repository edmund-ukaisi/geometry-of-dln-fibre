# Statement Card - A2 fixed-base triangular multiplier local boundedness

## Statement

At a continuous fixed-base paper chain, the deterministic p. 13 triangular
multiplier square-sum product

```text
squareSum([[I,0],[lowerLeftBlock S.L,I]])
  * squareSum([[I,-S.B],[0,I]])
```

has a positive local upper bound.  Relative to the source-rank stratum, this
bound and the self-base product-reduction certificate yield a positive
constant `c` such that

```text
(c/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= adaptedProductDifferenceSquareSum(x)
```

eventually on the fixed-base source-rank filter.

## Lean Names

```text
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
```

Supporting generic helpers:

```text
continuousAt_eventually_le_self_add_one
continuousAt_exists_pos_eventually_le
aoyagiCoordinateSquareSum_exists_pos_eventually_le_of_continuousAt
```

## Source

Aoyagi p. 13 triangular endpoint multipliers, plus the fixed-base
suffix-state field-continuity and self-base product-reduction certificate
already formalised in the A2 pipeline.

## Dependencies

- fixed-base suffix-state field continuity;
- automatic self-base recursive determinant-chart hypotheses;
- self-base product-reduction certificate neighborhood;
- source-filter adapted product-difference bound;
- finite real continuity/local-boundedness of square-sums.

## Nonclaims

No original DLN/statistical loss comparison, covariance lower bound, basis
norm equivalence, source-rank openness, analytic chart construction,
Jacobian/prior transport, regular-suspension theorem, normal crossings, pole
order, or RLCT extraction is proved.
