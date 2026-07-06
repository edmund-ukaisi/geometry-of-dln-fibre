# A2 Case 2 selected-entry product readback at the same radius

## Source calculation

The selected-entry product-coordinate pushforward already gives, for the
radius produced by the p.13 product-coordinate chart package,

```text
map selectedEntryProductChart selectedEntrySource
  =
map CedgeProd (valueReference.restrict domain).
```

Here

```text
domain = {value | value pivotNext != 0} x ball(0,R),
valueReference = (volume.restrict valueImage).prod
  (volume.restrict ball(0,R)).
```

The same p.13 chart package also provides a product readback

```text
productReadback : EdgeFamily -> valueCoordinates x regularCoordinates
```

with

```text
productReadback (CedgeProd z) = z       for z in domain,
CedgeProd (productReadback E) = E       for E in CedgeProd '' domain,
```

plus injectivity, continuity on `domain`, and measurability of the image.

Apply the generic source-side readback domination theorem with

```text
thetaReference = valueReference,
externalMeasure = map selectedEntryProductChart selectedEntrySource,
density = 1,
c = 1,
V = W = domain.
```

The weighted source identity required by the generic theorem is exactly the
selected-entry pushforward equality, since `withDensity 1` is the identity.
The density bound is tautological.  The result is, for every measurable chart
piece,

```text
map productReadback
  ((map selectedEntryProductChart selectedEntrySource).restrict chartPiece)
  <= valueReference.restrict domain.
```

This is a same-radius statement: the pushforward equality and the readback
package are both produced from the same p.13 radius witness.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_readback_le_valueReference_restrict_domain
```

## Boundary

This is measure/readback bookkeeping for the reduced p.13 selected-entry
product-coordinate chart.  It does not identify formal-product Haar,
determinant/raw Haar, original prior, normal crossings, pole order, or RLCT.
