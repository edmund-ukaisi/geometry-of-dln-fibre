# Statement Card - A2 selected-entry chart-image local handoff

Date: 2026-06-25.

## Claim

The local-source selected-entry signed-box finite-integral handoff specializes
to the concrete finite chart image `chartMap pivot '' signedBoxSet Rres`,
with `sourceChart = chartMap pivot` and base measure `volume`.  The finite
chart transport theorem supplies the weighted pushforward identity, and the
chart-image measurability theorem supplies the source measurability input.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

## Inputs Kept Explicit

- finite center and selected pivot;
- fixed-base regular-coordinate source data over the finite chart-image
  ambient space;
- edge-matrix measurability;
- positive signed-box radii;
- pivot integrability threshold;
- selected-entry residual identity along `chartMap pivot`;
- local loss and density bounds on `nhdsWithin x0 (chartMap pivot '' signedBoxSet Rres)`.

## Nonclaims

No source chart inside the original DLN parameter space is constructed.  No
source coverage, original-source measure identity, full DLN loss comparison,
normal-crossing certificate, pole-order computation, or RLCT extraction is
proved.

## Verification

Focused build passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure
```

Independent xhigh review passed:
`review-a2-selected-entry-chart-image-local-handoff.md`.
