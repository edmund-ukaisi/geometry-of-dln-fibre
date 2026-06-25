# Statement Card - A2 edge-matrix signed-box adapted-loss finite integral

Date: 2026-06-25.

## Claim

Under a measurable fixed-base edge-matrix family, the source-rank stratum is
measurable and the signed-box adapted-loss finite-integral front end no longer
needs global `Continuous Cedge`.

## Lean Artifacts

Expected additions:

```text
measurableSet_matrix_rank_le_of_measurable
measurableSet_matrix_rank_eq_of_measurable
measurableSet_paperEndpointFixedBaseSourceRankStratum_of_measurable_edgeMatrix
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
```

## Inputs Kept Explicit

- weighted signed-box source chart and pushforward;
- source-density a.e.-measurability, nonnegativity, and monomial upper bound;
- residual monomial lower bound;
- positive continuous product density at `(x0,0)`;
- product-coordinate adapted lower bound;
- adapted-to-loss comparison.

## Nonclaims

No product chart, source coverage, density/Jacobian transport,
product-coordinate lower-bound construction, original-loss comparison, normal
crossings, pole order, or RLCT extraction is proved here.

## Verification

Passed:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
cd lean && lake build DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure
```

The second build replayed many pre-existing Core/DLN warnings and completed
successfully.  Xhigh review passed in
`review-a2-edge-matrix-signed-box-adapted-loss-finite-integral.md`.
