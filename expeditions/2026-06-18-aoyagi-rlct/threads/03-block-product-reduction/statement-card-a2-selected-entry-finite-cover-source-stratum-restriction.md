# Statement Card - A2 selected-entry finite-cover source-stratum restriction

## Declaration

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean
```

## Statement

Assume the finite selected-entry sector-cover original-loss hypotheses:
per-pivot residual readout, adapted product-difference lower bound, density
nonnegativity and upper bound, `Sres_i <= Rres_i`, `1 < Rres_i`, and the
selected-entry critical exponent inequality for every pivot.

If a supplied open neighborhood `Ulocal` of `0` satisfies

```text
Ulocal inter sourceStratum subset Ulocal inter signedBoxSet Sres,
```

then there is an open neighborhood `U` of `0` such that the original-loss
integrand has finite lower integral over

```text
(volume.restrict (U inter sourceStratum)).prod nu.
```

## Role

This removes the need for a local equality with one fixed selected-entry chart
image in this finite-cover lane.  It is useful when a later source argument
can place the local source-rank stratum inside a finite selected-entry
coordinate box.

## Boundary

The theorem is only monotone restriction from a finite selected-entry box.
It does not prove the local inclusion, source-rank coverage, source/image
equality, source-prior transport, Jacobian compatibility, normal crossings,
pole order, or RLCT.
