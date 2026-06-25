# Statement Card - A2 selected-entry chart-image original-loss wrapper

Date: 2026-06-25.

## Claim

On the finite selected-entry chart image `chartMap pivot '' signedBoxSet Rres`,
the selected-entry local-measure theorem can be specialized to the original
fixed-endpoint-basis square-Frobenius loss `lossDLN`, provided the
adapted-product lower bound and local density bounds are supplied on that
finite chart image.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower
```

## Inputs Kept Explicit

- finite center and selected pivot;
- fixed-base regular-coordinate source data over the finite chart-image
  ambient space;
- edge-matrix measurability;
- positive signed-box radii;
- selected-entry pivot integrability threshold;
- residual identity along `chartMap pivot`;
- adapted-product lower bound on
  `nhdsWithin x0 (chartMap pivot '' signedBoxSet Rres)`;
- local nonnegativity and boundedness of the transported density on the same
  finite chart image.

## Nonclaims

No original p.13 source chart is constructed.  No source-rank stratum coverage,
original-source measure identity, derivation of the adapted-product lower
bound from an original source chart, normal-crossing certificate, pole-order
computation, or RLCT extraction is proved.

## Verification

Focused build passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure
```

Independent xhigh review passed:
`review-a2-selected-entry-chart-image-original-loss-wrapper.md`.
