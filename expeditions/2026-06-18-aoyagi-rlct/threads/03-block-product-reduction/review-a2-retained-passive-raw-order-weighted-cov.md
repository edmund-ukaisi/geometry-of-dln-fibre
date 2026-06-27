# Review - A2 Retained-Passive Raw-Order Weighted Change of Variables

Date: 2026-06-27.

Reviewer: xhigh read-only explorer `Aristotle the 4th`.

Verdict: accepted.  No blockers.

## Scope Reviewed

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesMeasure.lean
lean/DLNFibre.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-weighted-cov.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-weighted-cov.md
```

## Verdict Details

The use of Mathlib's
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` is exact.  The slice
supplies the required null-measurable set, within-derivative, and injectivity
hypotheses for the retained-passive raw-order tuple chart.

## Audit Notes

- The within-derivative input is valid: ambient differentiability of
  `topologyTupleEdgeRawOrder` at determinant-chart points gives
  `HasFDerivAt`, and then `HasFDerivWithinAt`.
- The injectivity and image facts used are the retained-passive raw-order
  chart facts, not the edge-family-valued map.
- The documentation stays within the proved boundary and explicitly excludes
  inverse density, determinant formula or continuity, source-prior
  pushforward, normal crossings, pole order, and RLCT.
- The import addition is Aoyagi-local.

## Nonblocking Notes

Callers may benefit from convenience corollaries that discharge the
`NullMeasurableSet` hypothesis using
`nullMeasurableSet_topologyTupleDetChartSet`.  This is a usability suggestion,
not a soundness issue.

Controller follow-up: added the convenience wrappers
`map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det'` and
`map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart'`.
The focused module build still passes.
