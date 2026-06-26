# Reproduction - A2 Case 2 source-chart CenterCoord alignment

Date: 2026-06-26.

Status: Lean target implemented as definitional equality.

## Source Boundary

Aoyagi's Case 2 displayed chart on pp. 19-20 is the selected-entry chart on
the old residual-block center

```text
case2ResidualBlockPivotEntries n S J
```

with displayed pivot `(J+1,J+1)`.  The chart sends the pivot coordinate to
the selected variable and all other center coordinates to the selected
variable times their normalized residual coordinates.

Lean already has two names for this same finite substitution:

```text
case2DisplayedSourceChartMap
SelectedEntrySignedBox.CenterCoord.chartMap
```

This slice aligns those names.  It does not identify the post-pivot product
`D_(J+1) * C'_+` with chart coordinates.

## Calculation

Let

```text
center = case2ResidualBlockPivotEntries n S J,
pivot = ((J+1,J+1) : center),
y : center -> real.
```

By definition,

```text
SelectedEntrySignedBox.CenterCoord.chartMap pivot y p
  = selectedEntryChartMap pivot.1 (y pivot)
      (SelectedEntrySignedBox.CenterCoord.sourceResidual y) p.1.
```

The displayed Case 2 source chart map is also defined by

```text
case2DisplayedSourceChartMap n hS hcont u residual q
  = selectedEntryChartMap (J+1,J+1) u residual q.
```

With `u = y pivot` and
`residual = SelectedEntrySignedBox.CenterCoord.sourceResidual y`, both sides
are definitionally the same expression.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`:

```text
case2DisplayedSourceChartMap_eq_selectedEntrySignedBoxCenterCoord_chartMap_apply
```

## Nonclaims

- No post-pivot product readout is proved.
- No successor source-chart readout is proved.
- No endpoint equivalence is constructed.
- No source image, chart coverage, weighted pushforward, analytic Jacobian,
  normal crossings, pole order, or RLCT theorem is proved.
