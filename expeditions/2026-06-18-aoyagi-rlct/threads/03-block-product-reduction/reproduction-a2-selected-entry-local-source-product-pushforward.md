# A2 selected-entry local-source product pushforward

## Source calculation

The selected-entry center-coordinate chart is

```text
Phi(y)_p = y_p,
Phi(y)_i = y_p y_i      (i != p).
```

On any set `s` contained in the nonzero-pivot locus `{y_p != 0}`, the chart is
injective and has derivative determinant

```text
|det DPhi(y)| = |y_p|^(#(center \\ {p})).
```

Thus the already formalized change-of-variables identity holds on any
null-measurable local source set `s` with `s subset {y_p != 0}`:

```text
map Phi ((volume.restrict s).withDensity sourceDensity)
  = volume.restrict (Phi '' s).
```

Taking a product with any s-finite side measure `nu` gives

```text
map (Phi x id)
  (((volume.restrict s).withDensity sourceDensity).prod nu)
  =
  (volume.restrict (Phi '' s)).prod nu.
```

Composing with a downstream chart `F` preserves the identity, and adding an
extra downstream image density `density` commutes with the pushforward on both
sides:

```text
map (F o (Phi x id))
  ((((volume.restrict s).withDensity sourceDensity).prod nu)
    .withDensity (density o F o (Phi x id)))
  =
map F
  ((((volume.restrict (Phi '' s)).prod nu)
    .withDensity (density o F))).
```

## Aoyagi link

This is the local-source version of the pp.19-21 selected-entry nonzero-pivot
coordinate change.  It is needed because later local boundedness information
is naturally attached to a smaller supported source piece, not necessarily to
the whole punctured signed box.

## Lean targets

```text
SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_of_subset_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.map_prod_chartMap_id_restrict_withDensity_sourceDensity_eq_restrict_image_prod_of_subset_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_withDensity_sourceDensity_eq_map_restrict_image_prod_of_aemeasurable_of_subset_pivot_ne_zero
SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_withDensity_sourceDensity_withDensity_comp_eq_map_restrict_image_prod_withDensity_of_subset_pivot_ne_zero
```

## Boundary

These are selected-entry chart-produced measure identities only.  They do not
assert source coverage, choose a local source set, construct an Aoyagi original
prior, identify formal-product Haar, determinant/raw Haar, source/product
transport, normal crossings, pole order, or RLCT.
