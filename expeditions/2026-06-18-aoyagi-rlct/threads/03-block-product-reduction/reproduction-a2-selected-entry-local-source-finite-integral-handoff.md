# Reproduction - A2 selected-entry local-source finite-integral handoff

Date: 2026-06-25.

## Scope

This slice plugs the selected-entry signed-box monomial-unit calculation into
the existing local-source p.13 finite-integral socket.  It removes the generic
residual-unit and density-unit hypotheses when the residual chart is the
center-indexed selected-entry chart.

It does not construct the local source chart, prove the weighted pushforward
identity, prove chart coverage, prove analytic Jacobian/source-density
transport, compare to the full original loss, produce normal crossings,
compute pole order, or extract RLCT.

## Pen-And-Paper Calculation

Let `E` be a finite selected-entry center and let `p in E` be the pivot.  Use
center-indexed signed-box coordinates `z : E -> R`.  Write `u = z_p`.

The selected-entry chart sends

```text
x_p = u,
x_e = u z_e  for e != p.
```

The finite residual square-sum is

```text
res(z) = sum_{e in E} x_e^2
       = u^2 * (1 + sum_{e != p} z_e^2).
```

Thus

```text
res(z) = residualUnit(z) * prod_{e in E} |z_e|^(2 k_e),
```

where

```text
residualUnit(z) = 1 + sum_{e != p} z_e^2,
k_p = 1,
k_e = 0 for e != p.
```

The pointwise lower bound is

```text
1 <= residualUnit(z).
```

For the formal pivot-first determinant, the absolute density model is

```text
sourceDensity(z) = |u|^(|E|-1).
```

Equivalently,

```text
sourceDensity(z) = densityUnit(z) * prod_{e in E} |z_e|^(h_e),
```

where

```text
densityUnit(z) = 1,
h_p = |E|-1,
h_e = 0 for e != p.
```

The signed-box integrability criterion in the local-source socket is

```text
2 t k_e < h_e + 1
```

for every coordinate `e`.  For `e = p`, this becomes

```text
2 t < |E|.
```

In Lean the pivot-side input is kept as

```text
2 * t < (E.erase p).card + 1,
```

which is definitionally aligned with the selected-entry density exponent.  For
`e != p`, the condition is immediate because `k_e = h_e = 0`.

Consequently, once a supplied local source chart `sourceChart : (E -> R) -> α`
has

```text
squareResidual(sourceChart z) = selectedEntryResidual_p(z),
```

and once the supplied measure identity is

```text
μ.restrict source
  = map sourceChart (signedBox(E,Rres).withDensity (ofReal sourceDensity)),
```

the existing local-source signed-box finite-integral theorem applies with
`cres = Cres = 1`.

## Lean Landing

The new module is
`lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean`.

Main Lean name:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

It consumes:

- a local source `source : Set α` and its measurability;
- a center-indexed source chart `sourceChart : (center -> R) -> α`;
- the weighted pushforward identity using
  `SelectedEntrySignedBox.CenterCoord.sourceDensity pivot`;
- the residual-coordinate identification with
  `SelectedEntrySignedBox.CenterCoord.residual pivot`;
- the pivot critical inequality
  `2 * t < (center.erase pivot.1).card + 1`;
- the fixed-base edge-matrix measurability and p.13 local loss/density bounds.

It proves the same finite local integral conclusion as the generic local-source
monomial-unit socket.

## Remaining Boundary

Still not proved:

- existence of the local selected-entry source chart in the fixed-base source;
- the weighted pushforward identity;
- analytic Jacobian/source-density transport from the actual parameter source;
- source coverage or transition regularity;
- residual positivity/integrability for a produced chart beyond the local
  socket conclusion;
- comparison to the full original loss unless a downstream original-loss
  consumer is supplied;
- normal crossings, pole order, or RLCT extraction.
