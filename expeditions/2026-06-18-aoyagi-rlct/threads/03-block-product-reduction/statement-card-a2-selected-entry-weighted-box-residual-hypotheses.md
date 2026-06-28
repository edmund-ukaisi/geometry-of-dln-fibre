# Statement card - A2 selected-entry weighted-box residual hypotheses

## Declaration

```text
DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.
  residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

## Statement

For a selected-entry center chart with pivot `pivot`, positive signed-box
radii `R`, and exponent parameter `t >= 0`, if

```text
2 * t < ((center.erase pivot.1).card : R) + 1,
```

then under the weighted signed-box measure

```text
signedBox.withDensity
  (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y)),
```

the selected-entry residual is positive almost everywhere and

```text
integral^- ofReal ((SelectedEntrySignedBox.CenterCoord.residual pivot y)^(-t))
```

is finite.

## Role

This banks the selected-entry model's actual residual positivity and finite
negative-power integrability under its own formal Jacobian density.

## Boundary

This does not discharge the retained-passive canonical chart-side hypotheses:
that still requires a source-production/pushforward bridge from retained-
passive determinant-chart coordinates to selected-entry signed-box coordinates.
No original prior transport, normal-crossing extraction, pole order, or RLCT is
proved.
