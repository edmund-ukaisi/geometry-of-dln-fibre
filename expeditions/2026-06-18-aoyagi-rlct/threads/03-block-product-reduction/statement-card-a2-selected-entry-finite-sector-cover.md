# Statement card - A2 selected-entry finite sector cover

## Declarations

```text
DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.
  mem_chartMap_image_signedBoxSet_of_pivot_abs_max
DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.
  exists_pivot_abs_le_abs_of_ne_zero
DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.
  exists_maxPivot_mem_chartMap_image_signedBoxSet_of_mem_signedBoxSet_ne_zero
DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.
  signedBoxSet_subset_iUnion_chartMap_image_signedBoxSet_of_one_lt
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

## Statement

If `S i <= R i` for every finite center coordinate and `1 < R i` for every
target selected-entry radius, then

```text
signedBoxSet S subset union pivot, chartMap pivot '' signedBoxSet R.
```

The proof chooses a coordinate of maximal absolute value as pivot for nonzero
points and uses the fixed-pivot horn characterization.

## Role

This is finite all-pivot sector bookkeeping for selected-entry charts.  It
records the elementary bounded cover that follows from the fixed-pivot
chart-image theorem.

## Boundary

This does not prove local source-stratum coverage, source/image equality,
fixed-base source-chart construction, residual-product matrix identity,
source-measure identification, normal crossings, pole order, or RLCT.
