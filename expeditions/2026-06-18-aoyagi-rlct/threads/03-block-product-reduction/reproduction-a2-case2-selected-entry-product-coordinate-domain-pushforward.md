# A2 Case 2 selected-entry product-coordinate domain pushforward

## Source calculation

This note records the small support calculation that turns the landed
selected-entry product-coordinate pushforward into the exact source-domain
shape used by the p.13 product-coordinate handoff.

For Case 2 data, set

```text
center    = case2ResidualBlockPivotEntries n S (J+1)
pivotNext = (J+2,J+2) in center
```

and for selected-entry box radii `Rbox` let

```text
S0 = signedBoxSet Rbox cap {y | y pivotNext != 0}.
I0 = chartMap pivotNext '' S0.
```

The selected-entry chart satisfies

```text
chartMap pivotNext y pivotNext != 0 <-> y pivotNext != 0.
```

Hence `I0` lies in the value-coordinate source

```text
source = {value | value pivotNext != 0}.
```

## Domain support

Let the p.13 package choose `0 < R <= Rmax`, and set

```text
regularMeasure = volume.restrict ball(0,R)
domain = source x ball(0,R)
valueReference = (volume.restrict I0).prod regularMeasure.
```

The left factor of `valueReference` is supported on `I0`, hence on `source`.
The right factor is supported on `ball(0,R)` by definition of
`regularMeasure`.  Therefore

```text
valueReference.restrict domain = valueReference.
```

This support identity is independent of the p.13 chart map.  It is only the
selected-entry coordinate support calculation.

## Pushforward shape

The landed theorem gives

```text
map (fun (y,u) => CedgeProd(chartMap pivotNext y,u)) selectedEntrySource
  =
map CedgeProd valueReference.
```

Using the support identity rewrites the right side to

```text
map CedgeProd (valueReference.restrict domain).
```

This is the same-radius source-reference form needed by downstream product
handoffs.  It should not be obtained by independently composing two
existential radius-shrinking theorems, since those radii need not match.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_eq_map_valueReference_restrict_domain
```

## Boundary

This proves only a domain-shaped version of the selected-entry source/reference
pushforward through the reduced p.13 product-coordinate chart.  It does not
identify formal-product Haar, determinant/raw Haar, original prior, normal
crossings, pole order, or RLCT.
