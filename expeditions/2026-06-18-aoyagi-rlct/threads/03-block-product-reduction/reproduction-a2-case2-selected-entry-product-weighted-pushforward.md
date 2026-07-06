# A2 Case 2 selected-entry product weighted pushforward

## Source calculation

The selected-entry product pushforward already gives, for the p.13 radius
returned by the product-coordinate chart package,

```text
map selectedEntryProductChart selectedEntrySource
  =
map CedgeProd (valueReference.restrict domain).
```

Here `selectedEntryProductChart(y,u) = CedgeProd(chartMap pivot y,u)`, and

```text
selectedEntrySource =
  ((volume.restrict sourceSet).withDensity sourceDensity).prod regularMeasure,

valueReference =
  (volume.restrict valueImage).prod regularMeasure,

domain = {value | value pivot != 0} x ball(0,R).
```

The next elementary calculation is the same identity after adding a density
that depends only on the final edge-family point.  For any edge-side density

```text
density : EdgeFamily -> ENNReal
```

that is a.e. measurable on

```text
map CedgeProd (valueReference.restrict domain),
```

the weighted selected-entry source satisfies

```text
map selectedEntryProductChart
  (selectedEntrySource.withDensity
    (fun z => density (selectedEntryProductChart z)))
  =
map CedgeProd
  ((valueReference.withDensity
    (fun z => density (CedgeProd z))).restrict domain).
```

This is just functoriality of `withDensity` under a measurable map:

```text
map f (mu.withDensity (g o f)) = (map f mu).withDensity g.
```

Apply it once to the selected-entry chart side, once to the
value-coordinate product side, and use the unweighted selected-entry product
pushforward between the two middle terms.

This is the weighted source-side identity required by the generic p.13
product-coordinate handoff.  It is the step that lets a later theorem plug in
`density(E) = ofReal(phi(E))` for an original edge-family density, but it does
not itself construct or bound such a `phi`.

The same calculation also gives the bounded-density readback corollary.  If
`chartPiece` is measurable and

```text
density(E) <= c
```

for a.e. `E` with respect to

```text
(map CedgeProd (valueReference.restrict domain)).restrict chartPiece,
```

then the generic p.13 readback handoff applies with

```text
externalMeasure =
  map selectedEntryProductChart
    (selectedEntrySource.withDensity
      (fun z => density (selectedEntryProductChart z))).
```

The weighted selected-entry identity supplies the handoff's source-side
`withDensity` equality, using the same radius and the same domain-support
rewrite `valueReference.restrict domain = valueReference`.  The conclusion is

```text
AEMeasurable productReadback (externalMeasure.restrict chartPiece)

map productReadback (externalMeasure.restrict chartPiece)
  <= c • valueReference.restrict domain.
```

This is still a chart-produced selected-entry statement.  The bounded density
is supplied externally; bounding an actual Aoyagi prior density
`phi(CedgeProd(value,u))`, with or without the p.13 inverse-Jacobian unit, is a
separate local boundedness theorem.

## Aoyagi link

Aoyagi's p.13 reduction writes the product loss in the reduced variables
after the block elimination of Theorem 3.  The later blow-up induction
introduces selected pivot charts with a monomial Jacobian factor.  The Lean
selected-entry chart `chartMap` and source density `sourceDensity` encode that
finite-dimensional pivot chart.  The calculation here is the elementary
measure-theoretic statement that this selected-entry chart remains valid after
multiplying by any density pulled back from the image.

## Lean targets

Generic target:

```text
SelectedEntrySignedBox.CenterCoord.map_comp_prod_chartMap_id_restrict_nonzeroSignedBox_withDensity_sourceDensity_withDensity_comp_eq_map_restrict_image_prod_withDensity
```

Case 2 p.13 target:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_withDensity_eq_map_valueReference_withDensity_restrict_domain
```

Case 2 bounded-readback target:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_selectedEntrySource_withDensity_readback_le_smul_valueReference_restrict_domain
```

## Boundary

This is selected-entry product-chart measure bookkeeping.  It does not
identify formal-product Haar, determinant/raw Haar, original volume, original
prior transport, normal crossings, pole order, or RLCT.  It also does not
assert nonempty source boxes or positive mass; `Rbox` remains an explicit
input.
