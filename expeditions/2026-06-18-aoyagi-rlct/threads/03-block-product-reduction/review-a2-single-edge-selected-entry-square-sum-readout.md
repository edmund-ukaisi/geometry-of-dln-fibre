# Review - A2 single-edge selected-entry square-sum readout

Date: 2026-06-25.

Reviewer mode: controller review after xhigh scout recommendation.

## Verdict

Pass at the source-neutral one-edge square-sum boundary.

## Scope Check

The theorem is a scalar consequence of the previous one-edge selected-entry
coordinate readout.  It proves that the residual coordinate map at `(y,u)` has
the same Aoyagi square-sum as `SelectedEntrySignedBox.CenterCoord.chartMap pivot y`.
The proof then uses the selected-entry identity

```text
SelectedEntrySignedBox.CenterCoord.residual pivot y
  = aoyagiCoordinateSquareSum
      (SelectedEntrySignedBox.CenterCoord.chartMap pivot y).
```

The finite equivalence `residualCoordEquiv` is only used to reindex the finite
sum.  The determinant-unit hypothesis is inherited unchanged from the
coordinate readout theorem.

## Risks To Keep Explicit

- This is one-edge only.
- The first parameter of the product-coordinate family is `y`, not a source
  point `chartMap pivot y`.
- It does not discharge source coverage, source-stratum equality, local lower
  bounds, density hypotheses, measure transport, normal crossings, pole order,
  or RLCT.

Focused `SelectedEntryOriginalLossLocalMeasure` build passed.  Full
`DLNFibre` build, forbidden-marker scan, and diff check also passed.
