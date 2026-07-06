# A2 Case 2 selected-entry local-source readback with density one

## Source calculation

The local-domain weighted theorem gives the following statement on a supplied
local source piece `localSource` and a supplied regular-coordinate piece
`regularSet`:

```text
map productReadback
  (map selectedEntryProductChart
    (localSelectedEntrySource.withDensity
      (density o selectedEntryProductChart)))
  <= c * localValueReference.restrict localDomain,
```

provided `density(CedgeProd z) <= c` for every `z` in `localDomain`.

Set

```text
density(E) = 1,
c = 1.
```

Then `density(CedgeProd z) <= c` is the tautology `1 <= 1`, and

```text
localSelectedEntrySource.withDensity 1 = localSelectedEntrySource.
```

The scalar on the right also disappears:

```text
1 * localValueReference.restrict localDomain
  = localValueReference.restrict localDomain.
```

Thus the local selected-entry source measure itself satisfies

```text
map productReadback
  (map selectedEntryProductChart localSelectedEntrySource)
  <= localValueReference.restrict localDomain.
```

The a.e.-measurability conclusion is inherited from the same specialization.

## Aoyagi link

This is the local-source version of the same-radius selected-entry readback
bookkeeping for the p.13 reduced product-coordinate chart and the pp.19-21
selected nonzero-pivot chart.  The calculation is elementary measure
bookkeeping after the selected-entry local-source change of variables has
already been formalized.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_localSelectedEntrySource_readback_le_localValueReference_restrict_localDomain
```

## Boundary

This is only the density-`1` specialization of the supported local-domain
selected-entry product-coordinate handoff.  It does not construct or identify
an original prior, Haar transport, source coverage, source-rank coverage,
normal crossings, pole order, or RLCT.
