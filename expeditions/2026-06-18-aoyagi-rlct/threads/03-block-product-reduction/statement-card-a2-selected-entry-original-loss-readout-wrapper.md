# Statement card - A2 selected-entry original-loss readout wrapper

## Lean Artifact

File: `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`.

Name:

- `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_of_residualBlockCoordinateReadout`

## Statement

Lean now exposes the strongest selected-entry local source-stratum
original-loss endpoint using an explicit residual-coordinate readout instead
of the raw scalar square-sum equality.

The theorem still assumes a local equality between the source stratum and the
finite selected-entry chart image.  It additionally assumes an equivalence
between fixed-base residual indices and selected-entry center coordinates, and
pointwise readout of each residual coordinate along the selected-entry chart.

## Proved

The theorem derives the old `hresidual_eq` scalar square-sum hypothesis from:

- finite square-sum invariance under reindexing;
- the selected-entry residual square-sum identity;
- the supplied pointwise fixed-base residual coordinate readout.

It then delegates to the existing local source-stratum original-loss endpoint.

## Not Proved

No source-stratum coverage, all-pivot analytic atlas, source-measure transport,
fixed-base residual readout construction, analytic Jacobian identity, normal
crossings, pole order, or RLCT.

## Reproduction

- `reproduction-a2-selected-entry-original-loss-readout-wrapper.md`.

## Verification

- `env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure`
