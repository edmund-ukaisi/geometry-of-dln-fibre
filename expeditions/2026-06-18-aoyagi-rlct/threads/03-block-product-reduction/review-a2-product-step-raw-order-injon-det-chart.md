# Review - A2 product-step raw-order injectivity on determinant chart

Date: 2026-06-26.

Verdict: accepted at the stated scope.

## Checks

- The theorem is restricted to the determinant-chart set, exactly where
  `productReductionStepCoordinate_left_inverse` applies.
- The proof uses the existing inverse formula for the record-level coordinate
  change. It does not re-prove or alter the p. 13 algebra.
- The coordinate reorder is used only through injectivity of
  `productReductionStepChartTangentRawOrderEquiv`.
- The helper tuple-injectivity theorems are definitional record/tuple
  bookkeeping and do not introduce new mathematical hypotheses.

## Boundary

This is one of the hypotheses needed by Mathlib's Jacobian
change-of-variables theorem. It is not the theorem itself. A measure adapter
still needs a source set with a fixed measurable-space/additive-Haar measure
instance and a normed-space-aligned derivative family. Do not infer density
transport, source coverage, normal crossings, pole order, or RLCT from this
injectivity result alone.

