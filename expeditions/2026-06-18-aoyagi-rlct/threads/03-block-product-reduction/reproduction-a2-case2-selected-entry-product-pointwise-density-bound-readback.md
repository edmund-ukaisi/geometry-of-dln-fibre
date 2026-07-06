# A2 Case 2 selected-entry product pointwise density-bound readback

## Source calculation

The previous selected-entry weighted readback theorem assumes an image-side
a.e. bound

```text
density(E) <= c
```

with respect to

```text
(map CedgeProd (valueReference.restrict domain)).restrict chartPiece.
```

For later local-density work it is useful to expose the stronger but simpler
input

```text
forall z in domain, density(CedgeProd z) <= c.
```

The product-coordinate readback package already says:

```text
forall z in domain, productReadback(CedgeProd z) = z,
injOn CedgeProd domain,
forall E in CedgeProd '' domain,
  productReadback E in domain and CedgeProd(productReadback E) = E.
```

It also gives a.e. measurability of `CedgeProd` on any measure restricted to
`domain`, so the pushed reference measure is supported on
`CedgeProd '' domain`:

```text
almost every E for map CedgeProd (valueReference.restrict domain)
  lies in CedgeProd '' domain.
```

Restricting to `chartPiece` preserves this a.e. support property.  For such an
`E`, choose `z = productReadback E`.  Then `z in domain` and
`CedgeProd z = E`, so the pointwise bound gives

```text
density(E) = density(CedgeProd z) <= c.
```

This proves the image-side a.e. bound required by the selected-entry weighted
readback theorem, with the same radius and the same product-coordinate domain.

## Aoyagi link

This is elementary measure/readback bookkeeping around Aoyagi's p.13 reduced
product-coordinate variables and the pp.19-21 selected-entry nonzero-pivot
chart.  It is designed to be combined later with a local continuity argument
for a concrete density such as `ofReal(phi(E))`; the local continuity argument
must still supply the pointwise bound on the selected-entry product domain or
on a smaller supported piece.

## Lean target

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_withDensity_readback_le_smul_valueReference_restrict_domain_of_forall_density_comp_le
```

## Boundary

This theorem does not construct or bound an Aoyagi prior density.  It does not
shrink the selected-entry residual box into a topological neighborhood, prove
formal-product Haar, determinant/raw Haar, original volume, original-prior
transport, source-rank coverage, normal crossings, pole order, or RLCT.  It is
only the pointwise-to-a.e. density-bound adapter for the selected-entry
chart-produced product measure.
