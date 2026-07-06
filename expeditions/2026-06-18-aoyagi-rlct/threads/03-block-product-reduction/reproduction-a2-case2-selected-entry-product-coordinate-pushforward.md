# A2 Case 2 selected-entry product-coordinate pushforward

## Source calculation

This is the p.13 specialization of the selected-entry source/reference change
of variables.

For Case 2 data, set

```text
center    = case2ResidualBlockPivotEntries n S (J+1)
pivotNext = (J+2,J+2) in center
```

and let

```text
S0 = signedBoxSet Rbox cap {y | y pivotNext != 0}.
```

The selected-entry value coordinate is

```text
value = chartMap pivotNext y.
```

On `S0`, the value coordinate has nonzero pivot because

```text
chartMap pivotNext y pivotNext != 0 <-> y pivotNext != 0.
```

Thus the image

```text
I0 = chartMap pivotNext '' S0
```

lies inside the p.13 value-coordinate source

```text
source = {value | value pivotNext != 0}.
```

## p.13 chart

The p.13 base source chart must be defined on value coordinates:

```text
sourceChart(value)
  = retained-passive p.13 source edge family
      (retainedData(preimageOfPivotNeZero pivotNext value)).
```

This distinction is essential.  If the p.13 source chart were fed raw
selected-entry coordinates `y`, the residual readback would be
`chartMap pivotNext y`, not `y`.  Feeding value coordinates through
`preimageOfPivotNeZero` makes the residual readback recover `value`.

Let

```text
CedgeProd(value,u)
```

be the reduced p.13 product-coordinate edge-family map built from this
`sourceChart`.

The existing p.13 readback package supplies a radius `0 < R <= Rmax` such that
`CedgeProd` is continuous, injective, a.e. measurable for every measure
restricted to

```text
domain = source x ball(0,R),
```

and has the expected local readback on that domain.

## Measure calculation

Let

```text
regularMeasure = volume.restrict ball(0,R).
```

The selected-entry weighted source measure is

```text
((volume.restrict S0).withDensity
  (fun y => ofReal (sourceDensity pivotNext y))).prod regularMeasure.
```

The value-reference measure is

```text
(volume.restrict I0).prod regularMeasure.
```

Since `I0 subset source` and `regularMeasure` is supported on `ball(0,R)`,
the value-reference measure is supported on `domain`.  Therefore
`CedgeProd` is a.e. measurable for this measure by the p.13 package.

Applying the selected-entry product pushforward theorem with downstream chart
`CedgeProd` gives

```text
map (fun (y,u) => CedgeProd(chartMap pivotNext y, u))
  (((volume.restrict S0).withDensity sourceDensity).prod regularMeasure)
=
map CedgeProd ((volume.restrict I0).prod regularMeasure).
```

This is exactly the selected-entry source/reference equality for the actual
Case 2 p.13 product-coordinate chart.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_eq_map_valueReference
```

## Boundary

This proves only a chart-produced selected-entry weighted source pushforward
through the reduced p.13 product-coordinate chart.  It does not identify
formal-product Haar, determinant/raw Haar, original prior, normal crossings,
pole order, or RLCT.  The local inverse-Jacobian density bounds are a separate
bounded-unit input, not part of this pushforward equality.
