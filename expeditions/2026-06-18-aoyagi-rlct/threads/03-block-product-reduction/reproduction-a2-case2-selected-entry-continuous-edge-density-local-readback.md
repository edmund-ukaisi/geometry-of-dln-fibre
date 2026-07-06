# A2 Case 2 selected-entry continuous edge-density local readback

## Source calculation

Fix the selected-entry product-coordinate chart returned by the Case 2
same-radius handoff:

```text
CedgeProd : domain -> EdgeFamily,
productReadback : EdgeFamily -> domainAmbient,
valueReference : Measure domainAmbient.
```

The existing weighted selected-entry readback theorem already says that if a
downstream density `density : EdgeFamily -> ENNReal` is a.e. bounded by `c` on

```text
(map CedgeProd (valueReference.restrict domain)).restrict chartPiece,
```

then the product readback of the weighted selected-entry image over
`chartPiece` is bounded by

```text
c * valueReference.restrict domain.
```

Now take a real continuous edge-family density

```text
phi : EdgeFamily -> Real
density(E) = ENNReal.ofReal(phi(E)).
```

For any source point `z0 in domain`, set `E0 = CedgeProd z0` and

```text
mu = map CedgeProd (valueReference.restrict domain).
```

Since `phi` is continuous and `ENNReal.ofReal` is continuous, `density` is
continuous at `E0`.  Also `density(E0) < infinity`.  The local measure lemma
`exists_open_ae_restrict_le_of_continuousAt_lt_top` gives a finite constant
`c` and an open neighborhood `chartPiece` of `E0` such that

```text
density(E) <= c
```

for `mu.restrict chartPiece`-almost every `E`.  This is exactly the input of
the weighted selected-entry readback theorem.

## Aoyagi link

This is the elementary local bounded-density part of Aoyagi's p.13
product-coordinate calculation after the pp.19-21 selected-entry nonzero-pivot
chart.  It packages the fact that a supplied continuous downstream
edge-family density is locally bounded on the selected-entry product-coordinate
image, then reuses the already formalized selected-entry weighted pushforward
and product readback.

## Lean target

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_withDensity_ofReal_continuousEdgeDensity_readback_le_smul_valueReference_restrict_domain
```

## Boundary

This theorem does not assert that `phi` is the Aoyagi original prior density,
nor does it prove source/product-coordinate transport for such a prior.  It
does not shrink the selected-entry residual box into a source neighborhood,
identify formal-product Haar, determinant/raw Haar, original volume,
source-rank coverage, normal crossings, pole order, or RLCT.  It only supplies
the local image-side a.e. boundedness needed for the already proved
selected-entry weighted readback theorem.
