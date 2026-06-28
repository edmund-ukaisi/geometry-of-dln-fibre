# Statement card - A2 selected-entry target-image residual hypotheses

## Declaration

```text
DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.
  aoyagiCoordinateSquareSum_pos_ae_and_lintegral_rpow_neg_restrict_chartMap_image
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean
```

## Statement

For a selected-entry center chart with pivot `pivot`, positive signed-box
radii `R`, and `t >= 0`, if

```text
2 * t < ((center.erase pivot.1).card : ℝ) + 1,
```

then under Lebesgue measure restricted to

```text
SelectedEntrySignedBox.CenterCoord.chartMap pivot ''
  SelectedEntrySignedBox.CenterCoord.signedBoxSet R,
```

the target-coordinate square-sum `aoyagiCoordinateSquareSum` is positive
almost everywhere and has finite lower integral of

```text
ofReal ((aoyagiCoordinateSquareSum x)^(-t)).
```

## Role

This transports the selected-entry weighted source-box residual theorem through
the finite selected-entry chart pushforward to the target chart-image measure.

## Boundary

This is still finite selected-entry target-coordinate analysis.  It does not
construct a retained-passive source chart, identify a retained-passive
determinant-chart measure, prove all-pivot cover integrability, transport an
original prior, produce normal crossings, compute pole order, or extract an
RLCT.
