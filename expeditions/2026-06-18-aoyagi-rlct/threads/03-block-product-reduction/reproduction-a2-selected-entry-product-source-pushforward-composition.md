# A2 selected-entry product source pushforward composition

Date: 2026-07-06.

## Question

After the selected-entry chart has been formalised on the center block, what
concrete source/reference measure identity can feed the p.13 product-coordinate
handoff without claiming raw-Haar transport?

The honest identity is not a determinant-chart Haar theorem.  It is the
selected-entry change of variables, stable under an arbitrary side product
measure and stable under any measurable downstream chart.

## Variables

Let `center` be the finite selected-entry center index set and let
`pivot : center`.  The source coordinate is

```text
y : center -> R.
```

The selected-entry chart is

```text
chartMap pivot y : center -> R.
```

The source density is

```text
sourceDensity pivot y = |det D(chartMap pivot)(y)|.
```

Lean already proves this determinant identity as

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_abs_chartMapFDeriv_det
```

and the nonzero-pivot chart change-of-variables identity as

```text
map_chartMap_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image.
```

Let `beta` be any side coordinate type with side measure `nu`; in the p.13
application this side coordinate is the regular-coordinate vector `u`.

Let

```text
S0 = signedBoxSet Rres cap {y | y pivot != 0}
I0 = chartMap pivot '' S0.
```

The weighted source measure is

```text
((volume.restrict S0).withDensity
  (fun y => ofReal (sourceDensity pivot y))).prod nu.
```

The value-coordinate reference measure is

```text
(volume.restrict I0).prod nu.
```

## Calculation

The one-block selected-entry theorem gives

```text
map (chartMap pivot)
  ((volume.restrict S0).withDensity sourceDensity)
=
volume.restrict I0.
```

Taking products with `nu` and using `Measure.map_prod_map` gives

```text
map (fun (y,u) => (chartMap pivot y, u))
  (((volume.restrict S0).withDensity sourceDensity).prod nu)
=
(volume.restrict I0).prod nu.
```

Now let

```text
F : (center -> R) x beta -> gamma
```

be any measurable downstream chart.  Applying `Measure.map F` and using
`Measure.map_map` gives

```text
map (fun (y,u) => F (chartMap pivot y, u))
  (((volume.restrict S0).withDensity sourceDensity).prod nu)
=
map F ((volume.restrict I0).prod nu).
```

For local p.13 charts, the downstream chart is often only packaged as
a.e.-measurable on the local reference measure.  The same calculation uses
`AEMeasurable.map_map_of_aemeasurable`: if `F` is a.e.-measurable with respect
to `(volume.restrict I0).prod nu`, the composed identity remains valid.

For the p.13 product chart, `F` will be the product-coordinate edge-family map
`CedgeProd`.  Thus this identity supplies the selected-entry value-coordinate
source/reference comparison.  It does not identify this pushed measure with
formal product Haar, determinant Haar, or the original prior; those are
separate steps.

## Agent audit integration

Anscombe identified the selected-entry product chart theorem as the strongest
already-proved concrete input and warned not to promote retained-passive
chart-layer identities to full raw-Haar transport.

Halley checked the Aoyagi dependency map: pp. 10-13 and pp. 19-21 support the
coordinate algebra and selected-entry Jacobian bookkeeping, but they do not
supply a finished global raw/source-prior measure identity.  Original-prior
density is a later smooth-unit comparison.

Tesla checked the product-step side: full raw determinant-chart change of
variables is formalised, but the p.13 section fixes transverse coordinates
(`C1 = I`, `A3 = 0`) and therefore cannot push to full raw Haar on the ambient
raw tuple space.

## Lean landed

The new reusable theorems are in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`:

```text
SelectedEntrySignedBox.CenterCoord.map_prod_chartMap_id_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image_prod

SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_signedBoxMeasure_withDensity_sourceDensity_eq_map_restrict_image_prod

SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_map_restrict_image_prod

SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_signedBoxMeasure_withDensity_sourceDensity_eq_map_restrict_image_prod_of_aemeasurable

SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_map_restrict_image_prod_of_aemeasurable
```

The first adds the punctured source version.  The latter two compose the
selected-entry product pushforward with an arbitrary measurable downstream
chart, and the final two weaken this to a.e. measurability on the
value-coordinate reference measure.

## Boundary

This is a source-coordinate identity for the selected-entry chart.  It does
not prove:

- a `CedgeProd` weighted identity for formal product Haar;
- full determinant/raw Haar transport for the p.13 section;
- original-prior transport;
- a normal-crossing chart;
- pole order or RLCT extraction.

Verification passed: focused Lean check, focused module build, full local
`lake build DLNFibre`, `scripts/sorries`, `git diff --check`, code-only
forbidden-marker scan, and direct axiom probes.  The new declarations report
only `[propext, Classical.choice, Quot.sound]`.

The next non-thin targets are:

- instantiate the composed theorem with the p.13 product chart and the local
  regular-coordinate ball, making the `thetaReference.restrict domain` support
  condition explicit;
- prove concrete local bounds for the p.13 inverse/raw-order density along the
  product coordinates, as Tesla recommended.
