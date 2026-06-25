# Statement card - A2 selected-entry residual coordinate square-sum

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`.

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiCoordinateSquareSum_comp_equiv`

File: `lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap`
- `DLNFibre.DLN.Aoyagi.SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_eq_residual_of_coord_readout`

## Statement

Lean now proves that the center-indexed selected-entry residual is exactly the
finite square-sum of the selected-entry chart coordinates.  It also proves a
source-neutral coordinate-readout bridge: if a finite coordinate family reads
those selected-entry chart coordinates up to an explicit equivalence of finite
index types, then its `aoyagiCoordinateSquareSum` is the selected-entry
residual.

## Source Role

This is the elementary finite square-sum algebra behind Aoyagi's displayed
selected-entry chart on PDF pp. 15-21.  It is the Lean-safe part of the
post-interruption source/API scout recommendation: remove only the purely
finite residual-coordinate algebra, and keep the analytic/source chart data
explicit.

## Proved

- Finite square-sums are invariant under equivalence of finite coordinate
  indices.
- `CenterCoord.residual pivot y =
  aoyagiCoordinateSquareSum (CenterCoord.chartMap pivot y)`.
- Any finite coordinate family pointwise equal to `CenterCoord.chartMap pivot y`
  after an explicit reindexing has square-sum equal to
  `CenterCoord.residual pivot y`.

## Assumed

The coordinate-readout bridge assumes an explicit equivalence of index types
and pointwise coordinate equality.  It does not construct that readout for the
fixed-base residual map.

## Not Proved

No p.13 source chart construction, source-stratum image/coverage, finite cover,
source-measure transport, fixed-base residual-coordinate readout, analytic
Jacobian/source-density identity, normal crossings, pole order, or RLCT.

## Reproduction

- `reproduction-a2-selected-entry-source-chart-coverage-boundary.md`.

## Verification

- `env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure`
