# Statement card - A2 selected-entry finite-cover integral assembly

## Declarations

```text
DLNFibre.DLN.Aoyagi.
  lintegral_prod_restrict_lt_top_of_subset_iUnion_finite

DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix

DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

## Files

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean
lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean
```

## Statement

If a smaller center signed box `signedBoxSet Sres` is covered by all
selected-entry chart images with target radii `Rres`, and every fixed-pivot
chart image has a finite local lower integral near `0`, then a finite local
lower integral holds over the smaller signed box.  The theorem obtains the
cover from

```text
Sres i <= Rres i,    1 < Rres i.
```

The original-loss wrapper instantiates the same finite-cover assembly with
the concrete square-Frobenius `lossDLN`, using the existing adapted-loss to
original-loss comparison constant.

## Role

This closes the finite atlas gluing step for selected-entry signed boxes.  It
turns per-pivot chart-image finite integrability into finite integrability on
a coordinate neighborhood covered by the finite selected-entry sectors.

## Boundary

This is not an Aoyagi source-stratum theorem.  It does not prove source/image
equality, original source-measure transport, analytic chart production,
Jacobian-density construction from original variables, normal crossings, pole
order, or RLCT.
