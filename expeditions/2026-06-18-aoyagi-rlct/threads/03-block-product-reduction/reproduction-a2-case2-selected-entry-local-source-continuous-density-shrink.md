# A2 Case 2 selected-entry local-source continuous-density shrink

## Source calculation

Let

```text
chi = SelectedEntrySignedBox.CenterCoord.chartMap pivotNext.
```

The local selected-entry source set is a source-coordinate set

```text
L0 subset {y | y pivotNext != 0},
```

and the corresponding value-coordinate domain is

```text
localDomain0 = chi '' L0 x G0.
```

The p.13 product-coordinate edge-family map is evaluated on value coordinates:

```text
CedgeProd(v,u).
```

The selected-entry product source chart is therefore

```text
(y,u) |-> CedgeProd(chi y, u).
```

For a supplied continuous real edge-family density `phi`, define

```text
density(E) = ENNReal.ofReal(phi(E)),
F(y,u) = density(CedgeProd(chi y,u)).
```

At a source-coordinate base point `(y0,u0) in L0 x G0`, continuity of `chi`,
continuity of the p.13 product-coordinate map on the nonzero-pivot cylinder,
continuity of `phi`, and continuity of `ENNReal.ofReal` give continuity of
`F` at `(y0,u0)`.  Since `F(y0,u0) < infinity`, there is a finite
`c : ENNReal` and a neighborhood of `(y0,u0)` on which

```text
F(y,u) <= c.
```

Extract a product neighborhood `Uy x Ug` from that neighborhood and set

```text
L = L0 inter Uy,
G = G0 inter Ug.
```

Then `L` and `G` are measurable, `L subset L0`,
`G subset G0`, and the base point remains in `L x G`.  The new value-side
domain is still product-shaped:

```text
localDomain = chi '' L x G.
```

For every `(v,u) in localDomain`, choose `y in L` with `v = chi y`.  Then
`(y,u) in Uy x Ug`, so

```text
density(CedgeProd(v,u))
  = density(CedgeProd(chi y,u))
  <= c.
```

This is exactly the pointwise density bound required by the supported
local-domain selected-entry readback theorem.  Applying that theorem gives

```text
map productReadback
  (map selectedEntryProductChart
    (localSelectedEntrySource.withDensity
      (density o selectedEntryProductChart)))
<=
c * localValueReference.restrict localDomain.
```

## Aoyagi link

This is the local bounded-density form of the p.13 product-coordinate
bookkeeping combined with the pp.19-21 selected nonzero-pivot chart.  The
argument is elementary topology and measure bookkeeping after the
selected-entry local-source change of variables and p.13 readback package have
already been formalized.

## Lean targets

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
```

Declarations:

```text
exists_measurableSet_prod_subset_of_mem_nhds_prod

PaperEndpointFixedBaseRegularCoordinateSourceData.continuousOn_case2EndpointTransport_selectedEntryValue_productCoordinate_CedgeProd_source_univ

PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_localSelectedEntrySource_withDensity_ofReal_continuousEdgeDensity_exists_shrink_readback_le_smul_localValueReference_restrict_localDomain
```

## Boundary

The theorem keeps `phi` as a supplied continuous edge-family density.  It does
not identify `phi` with Aoyagi's original prior, prove original-prior
transport, Haar transport, source coverage, source-rank coverage, residual
integrability, normal crossings, pole order, or RLCT extraction.

## Verification

Local verification passed on 2026-07-06:

```text
lake env lean DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
lake build DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryProductMeasureHandoff
lake build DLNFibre
scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan found no `sorry`, `admit`,
`axiom`, `native_decide`, or `#exit`.  Direct axiom probes for the three new
declarations reported only:

```text
[propext, Classical.choice, Quot.sound]
```

Xhigh read-only reviewer `Turing` found no issues.  The review specifically
checked the source-coordinate/value-coordinate handoff, product-shaped shrink,
continuity-to-finite-bound step, measurability of the shrunk pieces, use of
the existing weighted local-domain theorem, theorem scope, and nonclaim
boundary.
