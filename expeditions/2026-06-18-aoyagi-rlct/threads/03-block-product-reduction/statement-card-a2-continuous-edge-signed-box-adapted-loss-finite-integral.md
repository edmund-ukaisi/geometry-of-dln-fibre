# Statement Card - A2 continuous-edge signed-box adapted-loss finite integral

## Statement

A globally continuous fixed-base edge family, a supplied weighted signed-box
residual source chart, a positive continuous product density, a supplied
product-coordinate adapted lower bound, and a supplied positive comparison

```text
c0 * adaptedProductDifferenceSquareSum(CedgeProd(x,u)) <= loss(x,u)
```

imply local finiteness of the p.13 regular-coordinate integral for `loss`
after shrinking the regular-coordinate radius.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
```

## Dependencies

- fixed-base regular-coordinate source data;
- global `Continuous Cedge`;
- signed-box source chart a.e.-measurability and weighted pushforward;
- residual monomial lower bound and source-density monomial upper bound;
- product-coordinate adapted lower bound on `ball(0,Rmax)`;
- supplied positive comparison from adapted square-sum to `loss` on
  `ball(0,Rmax)`;
- positive continuous product density at `(x0,0)`;
- existing signed-box residual source theorem;
- existing continuous-density adapted-loss comparison theorem.

## Nonclaims

No signed-box chart or pushforward is constructed.  No density/Jacobian
transport, original `lossDLN` comparison, source-rank openness, product chart,
normal crossings, pole order, or RLCT extraction is proved.

