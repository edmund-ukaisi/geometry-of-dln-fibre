# Reproduction - A2 selected-entry signed-box monomial-unit data

Date: 2026-06-25.

## Scope

This slice turns the elementary selected-entry center-square calculation and
formal pivot-first determinant into signed-box monomial-unit data.  It is a
chart-side algebra package for the already-landed local-source signed-box
measure consumer.

It does not construct analytic chart domains, source coverage, a source
measure pushforward, an analytic Jacobian theorem, source-density transport,
normal crossings, pole order, or RLCT extraction.

## Pen-And-Paper Calculation

Let `E` be a finite center and let `p in E` be the selected pivot.  Use signed
box coordinates

```text
Coord_p = {*} disjoint_union (E \ {p}).
```

Write `u = z_*` and `y_e = z_e` for `e != p`.  The selected-entry chart is

```text
x_p = u,
x_e = u * y_e  for e != p.
```

Aoyagi's center-square convention is the finite square-sum

```text
residual(z) = sum_{e in E} x_e^2.
```

Substituting the chart gives

```text
sum_{e in E} x_e^2
  = u^2 + sum_{e != p} (u * y_e)^2
  = u^2 * (1 + sum_{e != p} y_e^2).
```

Over `R`, this becomes the signed-box absolute monomial identity

```text
residual(z)
  = residualUnit(z) * prod_i |z_i|^(2 * k_i),
```

where

```text
residualUnit(z) = 1 + sum_{e != p} y_e^2,
k_* = 1,
k_e = 0 for e != p.
```

The unit bound is pointwise:

```text
1 <= residualUnit(z),
```

because the remaining square-sum is nonnegative.

For the formal pivot-first coordinate change, the Jacobian matrix has block
form

```text
[1  0]
[y uI],
```

so its determinant is

```text
u^(|E|-1).
```

The signed-box density model uses the absolute formal determinant

```text
sourceDensity(z) = |u|^(|E|-1).
```

Equivalently,

```text
sourceDensity(z)
  = densityUnit(z) * prod_i |z_i|^(h_i),
```

where

```text
densityUnit(z) = 1,
h_* = |E|-1,
h_e = 0 for e != p.
```

Thus `0 <= densityUnit(z) <= 1`.  These are exactly the hypotheses consumed by
the generic signed-box monomial-unit inequality package, with constants
`c = 1` and `C = 1`.

## Source Anchors

The source-side audit ties this calculation to Aoyagi's Case 2 selected-entry
blow-up center on pp. 19-22, and to the existing A4 reproduction notes:

- `threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-sq-jacobian-a4.md`;
- `threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-unit-a4.md`;
- `threads/04-blow-up-certificate/audit-case2-source-production-pp19-22-insufficient-a4.md`.

The calculation used here is independent of the quiver paper.

## Lean Landing

The new bridge module is
`lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`.

Main Lean names:

```text
SelectedEntrySignedBox.Coord
SelectedEntrySignedBox.sourceResidual
SelectedEntrySignedBox.residual
SelectedEntrySignedBox.residualUnit
SelectedEntrySignedBox.sourceDensity
SelectedEntrySignedBox.sourceDensity_eq_abs_pivotFirstJacobian_det
SelectedEntrySignedBox.lossExp
SelectedEntrySignedBox.densityExp
SelectedEntrySignedBox.residual_eq_unit_mul_abs_monomial
SelectedEntrySignedBox.sourceDensity_eq_unit_mul_abs_monomial
SelectedEntrySignedBox.one_le_residualUnit
SelectedEntrySignedBox.densityUnit_nonneg
SelectedEntrySignedBox.densityUnit_le_one
SelectedEntrySignedBox.monomialUnitHypotheses
SelectedEntrySignedBox.monomialLower_sourceDensityBounds
```

The file also provides the center-subtype presentation
`SelectedEntrySignedBox.CenterCoord.*`.  In that version the signed-box index
is the finite center subtype itself; the pivot coordinate carries the
nonzero loss and density exponents, and all non-pivot coordinates carry zero
exponents.  This is a reindexing convenience for downstream Case 2 source
coordinates, not a new analytic claim.

The final theorem applies
`PaperEndpointFixedBaseRegularCoordinateSourceData.signedBox_monomialLower_sourceDensityBounds_of_monomialUnits`
to the concrete selected-entry data.

## Remaining Boundary

Still not proved:

- analytic chart domains or signed-box radii as source neighborhoods;
- chart coverage or transition regularity;
- source production or branch termination;
- weighted source-measure pushforward;
- analytic Jacobian or volume-form transport;
- identification of the actual transported density/prior;
- comparison from this finite residual-center square to the full DLN loss;
- normal-crossing extraction, pole order, or RLCT.
