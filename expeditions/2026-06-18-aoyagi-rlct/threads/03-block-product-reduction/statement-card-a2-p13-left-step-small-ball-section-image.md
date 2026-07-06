# Statement Card - A2 p.13 left-step small-ball section image

## Declaration

```text
DLNFibre.DLN.Aoyagi.
  exists_pos_radius_le_map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_ae_regular_mem_ball
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean
```

## Statement

For every `Rmax > 0`, there is `0 < R <= Rmax` such that, under fixed-base
edge-matrix measurability, any local measure on the p.13 `(x,u)` coordinates
supported a.e. on `u in ball(0,R)` satisfies

```text
Measure.map Y eta = Measure.map Phi (Measure.map X eta).
```

Here `X` is the actual p.13 left-step raw section, `Y` is the p.13 raw-order
target tuple, and `Phi` is the raw-order product-step map.

## Role

This removes the explicit raw determinant-chart support input from the
section-image theorem when fixed-base edge-matrix measurability is available
and the local coordinate measure is already supported in a sufficiently small
regular-coordinate ball.

## Boundary

This is the image statement for the reduced p.13 raw section, not a full
raw determinant-chart parameterisation.  The section fixes transverse raw
coordinates, so it cannot by itself push a coordinate measure to full raw Haar.

No full raw-Haar pushforward, no original source/prior transport, no source
coverage, no density identification, no normal crossings, no pole order, and
no RLCT.
