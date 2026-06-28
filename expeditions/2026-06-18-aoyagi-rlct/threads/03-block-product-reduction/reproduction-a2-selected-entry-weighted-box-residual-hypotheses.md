# Reproduction - A2 selected-entry weighted-box residual hypotheses

Date: 2026-06-28.

Status: controller pen-and-paper reproduction before Lean.  This is finite
selected-entry signed-box analysis only.

## Source/Boundary Anchor

Aoyagi's selected-entry chart has one pivot coordinate and multiplies every
other center coordinate by that pivot:

```text
Phi_p(y)_p = y_p,
Phi_p(y)_i = y_p y_i      for i != p.
```

The finite center square-sum therefore factors as

```text
sum_i Phi_p(y)_i^2 = y_p^2 * (1 + sum_{i != p} y_i^2).
```

The formal absolute Jacobian density of this pivot-first chart is

```text
|y_p|^(|center|-1).
```

The selected-entry signed-box measure is the product Lebesgue measure on
`|y_i| < R_i`, weighted by this density.

## Pen-And-Paper Check

Let

```text
rho(y) = sum_i Phi_p(y)_i^2
J(y) = |y_p|^(|center|-1).
```

On the signed box, product Lebesgue measure is almost everywhere supported on
points where every coordinate is nonzero.  Hence `|y_i| > 0` for all `i`
almost everywhere, and in particular

```text
rho(y) = (1 + sum_{i != p} y_i^2) * |y_p|^2 > 0.
```

For finite negative-power integrability under the weighted signed-box measure,
we must check

```text
integral rho(y)^(-t) J(y) dy < infinity.
```

The unit factor `1 + sum_{i != p} y_i^2` is bounded below by `1`, so

```text
rho(y)^(-t) J(y)
  <= |y_p|^((|center|-1) - 2t)
```

for `t >= 0`.  All non-pivot coordinates contribute exponent `0`.  Thus the
finite-side one-dimensional condition is

```text
(|center|-1) - 2t > -1,
```

equivalently

```text
2t < |center|.
```

In the Lean statement this is written as

```text
2 * t < ((center.erase pivot).card : R) + 1.
```

The existing monomial signed-box theorem already proves this finite integral
from the exponent inequalities

```text
2 * t * lossExp_i < densityExp_i + 1.
```

For the pivot this is exactly the displayed condition; for every non-pivot
coordinate it is `0 < 1`.

## Lean Target

Add in `SelectedEntrySignedBoxMeasure.lean`:

```text
SelectedEntrySignedBox.CenterCoord.residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity
```

It proves, for positive signed-box radii and
`2 * t < card(center.erase pivot) + 1`, that the center selected-entry
residual is positive a.e. and has finite negative-power lower integral under
the selected-entry weighted signed-box measure.

## Boundary

- Selected-entry finite coordinate model only.
- No retained-passive determinant-chart source production.
- No pushforward from retained-passive chart coordinates to selected-entry
  signed-box coordinates.
- No original DLN prior or source measure transport.
- No normal crossings, pole order, or RLCT extraction.
