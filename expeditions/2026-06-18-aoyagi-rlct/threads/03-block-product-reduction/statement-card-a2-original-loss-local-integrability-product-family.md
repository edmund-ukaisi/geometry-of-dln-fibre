# Statement Card - A2 original-loss local integrability for the product family

Date: 2026-06-25.

## Claim

For a multi-edge chain `N = M + 2`, a continuous self-based source family
`CedgeBase`, and the explicit source-dependent p.13 product-coordinate family
`CedgeProd`, the original `lossDLN` local finite-integral theorem can consume
the product-family lower bound directly.

Equivalently: the theorem no longer requires a separate hypothesis

```text
c * (residualSquareSum(x) + squareSum(u))
  <= adaptedProductDifferenceSquareSum(CedgeProd(x,u)).
```

for this explicit product family; the local product-family theorem supplies
the radius and positive constant.

## Lean Target

Planned Lean theorem in `DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
```

## Inputs Kept Explicit

- multi-edge shape `N = M + 2`;
- fixed-base complement data `U0, hU0`;
- continuous self-based source family `CedgeBase`;
- fixed bases for the original `lossDLN`;
- signed-box source chart and weighted pushforward;
- residual monomial lower bound and source-density monomial upper bound;
- transported density continuity and positivity at `(x0,0)`;
- positive analytic exponent parameter `t`.

## Nonclaims

No product-chart coverage, signed-box construction, source-measure
pushforward proof, density/Jacobian computation, normal-crossing certificate,
pole-order theorem, or RLCT extraction is proved.

## Verification

Focused build passed:
`env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure`.

Full build and hygiene passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre
scripts/sorries
git diff --check
```

The `scripts/sorries` summary was `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
