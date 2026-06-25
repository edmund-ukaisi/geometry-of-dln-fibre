# Review - A2 single-edge selected-entry product-coordinate readout

Date: 2026-06-25.

Reviewer mode: xhigh scout review plus controller integration.

## Verdict

Pass, at the finite one-edge readout boundary.

## Scope Check

The theorem is a specialization of the generic one-edge residual-matrix family.
It sets the supplied residual matrix to

```text
AoyagiResidualBlockCoordinateIndex.matrix
  (fun c =>
    SelectedEntrySignedBox.CenterCoord.chartMap pivot y
      (residualCoordEquiv c)).
```

The proof uses the generic one-edge readout theorem and then applies
`AoyagiResidualBlockCoordinateIndex.value_matrix`.  The continuity theorem uses
entrywise matrix continuity and `SelectedEntrySignedBox.CenterCoord.continuous_chartMap`.

Carver's xhigh Lean scout confirmed this is the shortest local Lean path and
that the inserted definitions match the intended `Dbase`.  Helmholtz's xhigh
boundary audit confirmed the honest statement: regular readout `u`, residual
readout through the supplied `residualCoordEquiv`, determinant-unit hypothesis
required, and continuity from the selected-entry chart map.

Focused `SelectedEntryOriginalLossLocalMeasure` build passed.  Full
`DLNFibre` build, forbidden-marker scan, and diff check also passed.

## Risks To Keep Explicit

- `residualCoordEquiv` is essential supplied finite data.
- `IsUnit det(Ctop(u))` remains a hypothesis.
- The selected-entry chart is not an inverse chart at pivot zero.
- This does not construct source coverage, source-measure transport, normal
  crossings, pole order, or RLCT.
