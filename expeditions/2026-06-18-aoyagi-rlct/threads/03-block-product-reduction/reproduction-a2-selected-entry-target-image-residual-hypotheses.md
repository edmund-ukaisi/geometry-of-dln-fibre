# Reproduction - A2 selected-entry target-image residual hypotheses

Date: 2026-06-28.

Status: controller pen-and-paper reproduction before Lean.  This is finite
selected-entry target-coordinate measure bookkeeping only.

## Source/Boundary Anchor

For a finite center chart with pivot `p`, the selected-entry source chart is

```text
chartMap_p(y)_p = y_p,
chartMap_p(y)_i = y_p y_i    for i != p.
```

The source-side residual and formal source density are

```text
residual_p(y) = aoyagiCoordinateSquareSum(chartMap_p(y)),
sourceDensity_p(y) = |y_p|^(|center|-1).
```

The previous selected-entry weighted-box theorem proves, under positive radii,
`t >= 0`, and `2*t < |center|`, that

```text
residual_p(y) > 0  a.e.
integral residual_p(y)^(-t) sourceDensity_p(y) dy < infinity
```

on the signed source box.  The selected-entry Jacobian theorem also proves

```text
map chartMap_p (signedBox.withDensity sourceDensity_p)
  = volume.restrict (chartMap_p '' signedBoxSet R).
```

## Pen-And-Paper Check

Let

```text
eta = signedBox.withDensity sourceDensity_p,
mu = volume.restrict (chartMap_p '' signedBoxSet R).
```

The map theorem gives `mu = map chartMap_p eta`.  For the target-coordinate
square-sum

```text
q(x) = aoyagiCoordinateSquareSum(x),
```

the selected-entry residual identity gives

```text
q(chartMap_p(y)) = residual_p(y).
```

For positivity, the source-side theorem gives `residual_p(y) > 0` for
`eta`-almost every `y`.  Pushing this a.e. statement through `chartMap_p` gives

```text
q(x) > 0
```

for `mu`-almost every `x`.

For finite negative-power integrability,

```text
integral q(x)^(-t) dmu(x)
  = integral q(chartMap_p(y))^(-t) deta(y)
  = integral residual_p(y)^(-t) deta(y)
  < infinity.
```

In Lean the map-integral step is used as the standard lower-integral
inequality against `Measure.map`; equality is not needed.

## Lean Target

Add in `SelectedEntrySignedBoxMeasure.lean`:

```text
SelectedEntrySignedBox.CenterCoord.
  aoyagiCoordinateSquareSum_pos_ae_and_lintegral_rpow_neg_restrict_chartMap_image
```

The theorem proves residual positivity almost everywhere and finite
negative-power lower integral for `aoyagiCoordinateSquareSum` under Lebesgue
measure restricted to the selected-entry chart image.

## Boundary

- Fixed selected-entry finite chart image only.
- No all-pivot finite-cover assembly.
- No retained-passive determinant-chart source production.
- No pushforward from retained-passive coordinates to selected-entry signed
  boxes.
- No original DLN source prior transport.
- No normal crossings, pole order, or RLCT extraction.
