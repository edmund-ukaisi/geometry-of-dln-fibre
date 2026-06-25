# Statement card - A2 selected-entry chart-image characterization

## Declaration

```text
DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.mem_chartMap_image_signedBoxSet_iff
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

## Statement

For a finite center, selected pivot, and positive signed-box radii `R`,
membership in the finite selected-entry chart image is characterized by:

```text
x in chartMap pivot '' signedBoxSet R
iff
x = 0
or
(x pivot != 0
  and |x pivot| < R pivot
  and forall i != pivot, |x i / x pivot| < R i).
```

## Role

This makes the finite selected-entry chart image explicit as the origin plus
a nonzero-pivot horn.  It is intended as source-facing chart-image
bookkeeping for later p.13 coverage work.

## Boundary

This is finite chart algebra only.  It does not prove local source-stratum
coverage, source-measure identification, residual-coordinate readout for the
fixed-base product coordinates, normal crossings, pole order, or RLCT.
