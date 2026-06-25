# Reproduction - A2 fixed-base product-family coordinate readout

Date: 2026-06-25.

Status: pen-and-paper reproduction for the finite readout from suffix-state
fields to the fixed-base p.13 coordinate maps.

## Source Boundary

Aoyagi p.13 uses the regular fields

```text
Ctop - I,    F2,    F3
```

and the cleaned residual field

```text
D = product_s C^(s).
```

In the fixed-base formalisation these are read from the deterministic suffix
state `S` as

```text
Ctop field      = S.Ctop,
F2 field        = -S.B,
F3 field        = lowerLeftBlock(S.L),
residual field  = S.D.
```

This note only records the finite readout.  It does not construct a product
edge-family, prove transformed-edge block shapes, prove a chart/Jacobian
statement, or extract an RLCT.

## Calculation

The fixed-base regular coordinate map is definitionally

```text
regularBlockCoordinateMap(Cedge,x)
  = value(S.Ctop - I, -S.B, lowerLeftBlock(S.L)).
```

Therefore if a suffix-field theorem supplies

```text
S.B = -F2,
S.Ctop = Ctop,
S.L = [I, 0; F3, I],
```

then

```text
regularBlockCoordinateMap(Cedge,x)
  = value(Ctop - I, F2, F3).
```

The only signs are:

```text
-S.B = -(-F2) = F2,
lowerLeftBlock([I, 0; F3, I]) = F3.
```

Similarly, the fixed-base residual coordinate map is definitionally

```text
residualBlockCoordinateMap(Cedge,x) = value(S.D).
```

So if the suffix theorem gives `S.D = D`, then

```text
residualBlockCoordinateMap(Cedge,x) = value(D).
```

Combining these gives the cleaned product-difference coordinate readout

```text
productDifferenceCoordinateMap(Cedge,x)
  = value(Ctop - I, F2, F3, D).
```

## Lean Target

Add fixed-base readout lemmas in `RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseRegularBlockCoordinateMap_eq_of_suffixState_fields
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_of_suffixState_D
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
```

These lemmas should be definition-unfolding bridges.  A later theorem can feed
them with `ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_*`
after a product family has supplied the transformed-edge block-shape
hypotheses.

The fixed-base product-family wrapper now landed for chains with at least two
edges:

```text
paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdges_succSucc
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdges_succSucc
```

The first theorem specializes the matrix-level suffix-field theorem to the
endpoint bases used by fixed-base coordinate maps.  The second theorem reads
the coordinate family as

```text
value(Ctop - I, F2, F3, residualProduct EMat last 0).
```

The residual coordinate is intentionally the residual product of the supplied
transformed edge matrices.  It is not an arbitrary final residual matrix.

## Boundaries

No fixed-base continuous edge maps are constructed here.  No theorem proves
that a concrete `CedgeProd` realizes the product-family transformed-edge
shapes.  No source coverage, signed-box pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT extraction is asserted.
