# Reproduction - A2 p.13 left-step small-ball section image

Date: 2026-06-26.

Status: controller pen-and-paper reproduction before Lean.  This is a
section-image consumer under local regular-coordinate ball support.

## Source Boundary

Aoyagi p.13 supplies elementary block-product reduction for the p.13 local
coordinates.  It does not supply full raw Haar measure on the ambient raw
determinant chart from the p.13 section.

The actual left-step raw tuple is still the section

```text
X(x,u) = (I,Dtail(x),F3(u),Ctop(u),-Ctop(u)*F2(u),0,C0(x)).
```

The raw-order target tuple is

```text
Y(x,u) = (Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x)).
```

Let `Phi` be the raw-order product-step map.

## Pen-And-Paper Check

The previous local support calculation gives, for every `Rmax > 0`, a radius
`0 < R <= Rmax` such that

```text
u in ball(0,R)  =>  X(x,u) in rawDetChart
```

for every base coordinate `x`.

Therefore, if a local measure `eta` on `(x,u)` is supported a.e. on the
regular-coordinate ball

```text
u in ball(0,R),
```

then `X(x,u)` lies in the raw determinant chart for `eta`-almost every
`(x,u)`.

On that chart, the pointwise product-step algebra gives

```text
Y(x,u) = Phi(X(x,u)).
```

After deriving a.e. measurability of `X` from fixed-base edge-matrix
measurability, pushforward functoriality gives

```text
Measure.map Y eta = Measure.map Phi (Measure.map X eta).
```

This is still only the image of the p.13 section image measure.

## Lean Target

Add in `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`:

```text
exists_pos_radius_le_map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_ae_regular_mem_ball
```

The proof should combine:

```text
exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball
map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
```

## Boundary

- Proves a small-ball wrapper around the p.13 section-image identity.
- Assumes fixed-base edge-matrix measurability and a.e. support of the local
  `(x,u)` measure in a sufficiently small regular-coordinate ball.
- No full raw-Haar pushforward.
- No source/image equality for the original DLN source.
- No source/prior transport.
- No density identification, normal crossings, pole order, or RLCT.
