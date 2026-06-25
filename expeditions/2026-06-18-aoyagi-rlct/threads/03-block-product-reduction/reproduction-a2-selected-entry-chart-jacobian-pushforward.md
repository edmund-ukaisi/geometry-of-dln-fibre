# Reproduction - A2 selected-entry chart Jacobian pushforward

Date: 2026-06-25.

## Scope

This slice proves the elementary measure transport for the finite
center-indexed selected-entry chart.  It starts from a finite center `E`, a
selected pivot `p in E`, and the chart

```text
Phi_p(y)_p = y_p,
Phi_p(y)_i = y_p * y_i  for i != p.
```

It does not construct a p.13 source neighborhood, prove that this chart covers
the original DLN source, compare the full DLN loss, produce normal crossings,
compute pole order, or extract RLCT.

## Pen-And-Paper Calculation

Write `u = y_p`.  In the standard basis ordered with `p` first, the derivative
of `Phi_p` has rows

```text
d(Phi_p)_p = d u,
d(Phi_p)_i = y_i d u + u d y_i  for i != p.
```

The Jacobian matrix is therefore

```text
[1  0]
[y  uI].
```

Subtracting `y_i` times the pivot row from each non-pivot row leaves the
diagonal matrix

```text
diag(1, u, ..., u),
```

so

```text
det D Phi_p(y) = u^(|E|-1).
```

The signed-box density is the absolute determinant:

```text
sourceDensity(y) = |y_p|^(|E|-1) = |det D Phi_p(y)|.
```

The chart is injective on `{u != 0}`.  If `Phi_p(y) = Phi_p(z)`, then the
pivot coordinates give `y_p = z_p`; for each `i != p`,

```text
y_p y_i = z_p z_i,
```

and division by the nonzero pivot gives `y_i = z_i`.

On the pivot hyperplane `{u = 0}`, the chart collapses all non-pivot
coordinates to the center zero point.  This is why the change-of-variables
theorem is applied first to a set contained in `{u != 0}`.  The full signed
box is recovered because:

```text
volume({u = 0}) = 0,
Phi_p(signedBox intersect {u = 0}) subset {x_p = 0},
volume({x_p = 0}) = 0.
```

Thus the full signed-box pushforward is

```text
(Phi_p)_* ( signedBoxMeasure with density |u|^(|E|-1) )
  = volume restricted to Phi_p(signedBox).
```

## Lean Landing

The implementation is in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`.

New main Lean names:

```text
SelectedEntrySignedBox.CenterCoord.signedBoxSet
SelectedEntrySignedBox.CenterCoord.signedBoxMeasure_eq_volume_restrict
SelectedEntrySignedBox.CenterCoord.measurableSet_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.volume_pivot_hyperplane_eq_zero
SelectedEntrySignedBox.CenterCoord.signedBoxSet_ae_eq_inter_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.chartMapFDeriv_det
SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_abs_chartMapFDeriv_det
SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image
SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet
SelectedEntrySignedBox.CenterCoord.chartMap_image_signedBoxSet_ae_eq_inter_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
```

## Source Anchors

This is the elementary selected-entry calculation behind Aoyagi Case 2 on
PDF pp. 19-22.  It uses the same pivot-first determinant calculation as the
earlier selected-entry square-sum/formal-Jacobian reproductions in
`threads/04-blow-up-certificate/`.

The proof is independent of the quiver paper.

## Remaining Boundary

Still not proved here:

- existence of the p.13 selected-entry source chart inside the original DLN
  parameter space;
- source image or coverage for that chart;
- equality between the original source measure and the chart-image restricted
  volume measure;
- comparison from the finite selected-entry residual to the full DLN loss;
- normal-crossing production, pole order, or RLCT extraction.
