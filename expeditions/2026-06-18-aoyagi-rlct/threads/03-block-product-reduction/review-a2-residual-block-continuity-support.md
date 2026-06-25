# Review - A2 residual block continuity support

Date: 2026-06-25.

Scope: local continuity of transformed Schur residual blocks and residual
products under recursive determinant-chart hypotheses, and the resulting
source-dependent p.13 product-coordinate edge-family continuity.

## Verdict

Accepted as a continuity-support and local product-family continuity slice.
The Lean statements keep the determinant-chart hypotheses explicit, which is
necessary because Schur residuals use matrix inversion.

## Checks

- The proof does not claim residual-factor continuity from `ContinuousAt E x0`
  alone; it also requires determinant-chart hypotheses at `x0`.
- `residualBlock` continuity is derived from continuous suffix-state `B`,
  continuous transformed edges, and continuity of the Schur-complement formula
  on the determinant chart.
- `residualProduct` continuity is derived from
  `suffixState_D_eq_residualProduct`, so no separate product induction is
  duplicated.
- Fixed-base edge matrix continuity uses existing fixed-basis coordinate
  functionals on continuous linear maps.
- The p.13 raw matrix continuity helpers are placed in the topology layer,
  not the algebra-only `ProductReduction.lean` import boundary.
- The fixed-base matrix realisation map is continuous because fixed bases
  identify prescribed matrices with linear maps, and finite-dimensional
  linear maps are continuous.
- The source-dependent product-coordinate matrix family is checked in the
  right endpoint, middle edge, and left endpoint cases separately; this
  matches the p.13 calculation and avoids treating the piecewise constructor
  as an opaque black box.
- The final edge-family continuity theorem is only a composition of the
  fixed-base edge-matrix continuity theorem, the matrix-family continuity
  theorem, and matrix realisation continuity.
- The self-base wrapper legitimately removes the explicit recursive chart
  inputs only under `CedgeBase x0 = reverseEdge B`, using the existing
  fixed-base self-base recursive determinant-chart theorem.

## Boundary

This slice proves local source-dependent product-family continuity under
explicit recursive chart hypotheses.  It should not be used as a product
chart, automatic recursive chart-neighborhood theorem, source coverage theorem,
rank-stratum openness theorem, measure-transport theorem, normal-crossing
certificate, pole-order theorem, or RLCT extraction.
