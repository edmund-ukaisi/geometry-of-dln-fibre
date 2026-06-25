# Statement Card - A2 selected-entry local source-stratum original-loss bridge

Date: 2026-06-25.

## Claim

If the source-rank stratum and the finite selected-entry chart image agree
after intersecting a supplied open neighborhood of the base point, then the
selected-entry original-loss finite-integral theorem may be stated over the
source-rank stratum after shrinking the final integration neighborhood.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
```

Supporting bridge lemmas:

```text
nhdsWithin_eq_of_mem_nhds_inter_eq
restrict_inter_eq_of_subset_inter_eq
```

## Inputs Kept Explicit

- open local equality neighborhood `Ulocal`;
- `x0 in Ulocal`;
- local equality
  `Ulocal ∩ sourceStratum = Ulocal ∩ chartMap pivot '' signedBoxSet Rres`;
- fixed-base regular-coordinate source data;
- edge-matrix measurability;
- positive signed-box radii and selected-entry pivot threshold;
- residual identity along `chartMap pivot`;
- positive continuous transported density.

## What Is Discharged

- source-stratum eventual adapted lower bound is transported to the finite
  chart-image filter using the local equality;
- density bounds are generated on the finite chart-image filter from
  continuity at `(x0,0)`;
- the finite chart-image original-loss wrapper is reused;
- the final open set is shrunk into `Ulocal`, so the restricted source-stratum
  measure is rewritten to the restricted chart-image measure.

## Nonclaims

No original p.13 source chart is constructed.  The local equality hypothesis is
not proved.  There is no source-rank chart coverage theorem, no original-source
Jacobian/prior transport theorem, no normal-crossing certificate, no pole-order
calculation, and no RLCT extraction.

## Verification

Focused build passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure
```

Independent xhigh review passed:
`review-a2-selected-entry-local-source-stratum-original-loss-bridge.md`.
