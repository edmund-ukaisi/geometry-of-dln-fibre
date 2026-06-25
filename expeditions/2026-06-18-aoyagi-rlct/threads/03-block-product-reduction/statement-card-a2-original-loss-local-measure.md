# Statement Card - A2 original loss local measure handoff

## Statement

Fix original bases

```text
b j : Basis (Fin (d j)) R (reverseVertex W j).
```

Let the original endpoint target be the base reversed-chain endpoint map
expressed in those bases:

```text
target = [chainMap(reverseVertex W, reverseEdge W B, 0, last)]_{b 0,b last}.
```

Under the same local p.13 source, signed-box, residual, product-density, and
adapted product-difference lower-bound hypotheses as the existing adapted-loss
front end, there are `R`, `C`, and an open source neighborhood `U` with
`0 < R <= Rmax` and `0 <= C` such that

```text
lintegral z,
  ofReal
    (1_{ball(0,R)}(u)
      * (lossDLN d target (chainMapMatrixTuple b (CedgeProd z)))
          ^ (-(t + regularVariableCount/2))
      * density z)
  < top
```

over `(mu.restrict (U inter sourceStratum)).prod nu`, with the usual Lean spelling
using the ball indicator on the regular-coordinate variable.

## Lean Names

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
```

## Dependencies

- `exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple`;
- `paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum`;
- `exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density`;
- `exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density`.

## Role In A2

This removes the supplied `c0 * adapted <= loss` hypothesis for the concrete
original square-Frobenius loss attached to a chain-coordinate tuple.  It is the
current strongest local finite-integral theorem whose conclusion contains
`lossDLN`.

## Nonclaims

No arbitrary-tuple comparison, no statistical/KL/covariance loss comparison,
no p.13 product-chart construction, no weighted pushforward proof, no
density/Jacobian transport, no proof of the adapted product-coordinate lower
bound, no normal-crossing theorem, no pole-order computation, and no RLCT
extraction is proved.
