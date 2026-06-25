# Statement Card - A2 adapted loss-comparison continuous-density finite integral

## Statement

Under a supplied product-coordinate adapted lower bound and a supplied positive
comparison

```text
c0 * adaptedProductDifferenceSquareSum(CedgeProd(x,u)) <= loss(x,u),
```

positivity and continuity of the product density at `(x0,0)` allow the p.13
finite-integral bridge to shrink the regular radius and prove local finiteness
for `loss`.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
```

## Dependencies

- fixed-base regular-coordinate source data;
- measurable fixed-base source-rank stratum;
- residual positivity and residual negative-power integrability on the source
  stratum;
- supplied product-coordinate adapted lower bound on `ball(0,Rmax)`;
- supplied positive comparison from adapted square-sum to `loss` on
  `ball(0,Rmax)`;
- positive continuous product density at `(x0,0)`;
- existing continuous-density local-bound theorem;
- existing adapted-loss comparison finite-integral bridge.

## Nonclaims

No comparison with the original DLN/statistical loss is proved.  No p.13
product chart, source coverage, coordinate identification, density/Jacobian
transport, residual source hypothesis, normal crossings, pole order, or RLCT
extraction is proved.

