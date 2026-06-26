# Review - A2 selected-entry finite-cover integral assembly

Date: 2026-06-26.

Reviewer: xhigh `Feynman`.

Verdict: pass.

## Scope Checked

The reviewer checked the new finite selected-entry cover integrability
assembly in:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean
lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean
```

with declarations:

```text
lintegral_prod_restrict_lt_top_of_subset_iUnion_finite
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

## Findings

No blocking findings.

The finite-cover measure lemma is measure bookkeeping only.  It uses product
restriction monotonicity and finite subadditivity, and does not assert any
source or chart coverage.

The all-pivot signed-box assembly keeps the basepoint fixed at `0`, intersects
the finitely many per-pivot neighborhoods, and uses only the finite
selected-entry cover of `signedBoxSet Sres` by chart images with `Rres > 1`.

The original-loss wrapper is a faithful comparison wrapper.  It obtains the
existing positive endpoint comparison constant, combines it with the supplied
adapted-product lower bound, and delegates to the finite-cover theorem over
the selected-entry coordinate box only.

## Boundary Check

The slice does not claim source-rank-stratum equality, source/image equality,
source-measure transport from original coordinates, analytic source-chart
production, normal crossings, pole order, or RLCT.

## Checks

The reviewer ran:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean
lake env lean DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean
```

Both targeted Lean checks passed.  The controller additionally ran the shared
Lake build-script checks recorded in the final verification log for this
slice.
