# Statement Card - A2 adapted product-difference loss-comparison finite integral

## Statement

If a supplied product-coordinate adapted square-sum lower bound gives

```text
c * (residualSquareSum(x) + squareSum(u))
  <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)),
```

and a supplied positive comparison gives

```text
c0 * adaptedProductDifferenceSquareSum(CedgeProd(x,u)) <= loss(x,u),
```

then the p.13 finite-integral bridge applies to `loss` with comparison
constant `c0 * c`.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss
```

## Dependencies

- fixed-base regular-coordinate source data;
- measurable fixed-base source-rank stratum;
- residual positivity and residual negative-power integrability on the source
  stratum;
- supplied product-coordinate adapted lower bound;
- supplied positive comparison from adapted square-sum to `loss`;
- supplied local nonnegative/bounded density;
- existing p.13 local finite-integral theorem.

## Nonclaims

The comparison with `loss` is not proved.  No p.13 product chart, source
coverage, coordinate identification, density/Jacobian transport, residual
source hypothesis, original `lossDLN` comparison, normal crossings, pole
order, or RLCT extraction is proved.

