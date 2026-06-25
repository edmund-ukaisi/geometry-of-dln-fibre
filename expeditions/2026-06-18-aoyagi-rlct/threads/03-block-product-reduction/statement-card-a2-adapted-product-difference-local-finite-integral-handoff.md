# Statement Card - A2 adapted product-difference local finite-integral handoff

## Statement

If a supplied product-coordinate edge family identifies the adapted fixed-base
product-difference square-sum with a chart loss and supplies the lower bound

```text
c * (residualSquareSumBase(x) + squareSum(u))
  <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)),
```

with side conditions `0 < R`, `0 < c`, `0 <= C`, and `0 < t`, then the
existing p.13 local finite-side theorem gives finite local lower integral of

```text
1_{ball(0,R)}(u)
  * chartLoss(x,u)^(-(t + regularCount/2))
  * density(x,u)
```

over a sufficiently small restricted source neighborhood times the regular
coordinate measure.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_chartLoss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_identified
```

## Dependencies

- fixed-base regular-coordinate source data;
- measurable fixed-base source-rank stratum;
- residual positivity and residual negative-power integrability on the source
  stratum;
- supplied product-coordinate adapted lower bound;
- supplied chart-loss identification;
- supplied local nonnegative/bounded density;
- existing p.13 local finite-integral theorem.

## Nonclaims

No product chart is constructed.  No source coverage, coordinate
identification, Jacobian/prior density transport, residual positivity,
residual integrability, original `lossDLN` comparison, normal crossings, pole
order, or RLCT extraction is proved.
