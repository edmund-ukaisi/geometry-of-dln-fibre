# Reproduction - A2 selected-entry chart-image local handoff

Date: 2026-06-25.

## Scope

This slice specializes the local-source selected-entry signed-box
finite-integral handoff to the concrete finite chart image

```text
source = Phi_p(signedBox),
Phi_p(y)_p = y_p,
Phi_p(y)_i = y_p * y_i  for i != p.
```

It discharges only the formal chart-measure inputs that are internal to this
finite model:

```text
hsource_meas,
hsourceChart,
hmap.
```

It does not identify `Phi_p(signedBox)` with a source neighborhood in the
original DLN parameter space.

## Pen-And-Paper Composition Check

The earlier local-source handoff assumes a source set `source`, a source
measure `mu`, and a chart `sourceChart` satisfying

```text
mu restricted to source
  = (sourceChart)_* (signedBoxMeasure with density sourceDensity).
```

For the finite selected-entry chart image, take

```text
source      = Phi_p(signedBox),
mu          = Lebesgue measure on center coordinates,
sourceChart = Phi_p.
```

The selected-entry chart Jacobian pushforward gives exactly

```text
(Phi_p)_* (signedBoxMeasure with density |y_p|^(|E|-1))
  = volume restricted to Phi_p(signedBox).
```

Reversing this equality gives the required `hmap`.  The source measurability
input is supplied by the chart-image measurability lemma.  The chart
a.e.-measurability input is supplied by continuity of `Phi_p`.

The remaining assumptions are unchanged:

- edge-matrix measurability on the finite chart image ambient space;
- positivity of signed-box radii;
- the pivot threshold `2*t < |E|-1 + 1`;
- equality between the fixed-base residual block square-sum along `Phi_p` and
  the selected-entry residual;
- local loss and density bounds on `nhdsWithin x0 Phi_p(signedBox)`.

Thus the theorem is a composition wrapper.  It removes repeated chart-measure
plumbing but still leaves the original-source problem outside the statement.

## Lean Landing

Implemented in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean` as

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

The proof delegates to

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

with the three chart-measure inputs filled by

```text
SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet
SelectedEntrySignedBox.CenterCoord.aemeasurable_chartMap
SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
```

## Remaining Boundary

Still not proved:

- source-image/coverage theorem in the original DLN parameter space;
- local equality between the original source measure and this finite chart
  image model;
- comparison between full DLN loss and the selected-entry residual on the
  original source;
- normal-crossing production, pole order, or RLCT extraction.
