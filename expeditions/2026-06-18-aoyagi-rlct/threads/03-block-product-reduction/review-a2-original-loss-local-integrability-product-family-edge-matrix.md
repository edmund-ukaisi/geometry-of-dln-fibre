# Review - A2 original-loss local integrability for the product family, edge-matrix form

Date: 2026-06-25.

Scope: review of the measurable-edge-matrix variant of the original `lossDLN`
local finite-integral theorem for the explicit self-base multi-edge p.13
product-coordinate family.

## Verdict

Accepted at the source-measure plumbing scope.

## Checks

- The theorem weakens the previous top product-family handoff from global
  `Continuous CedgeBase` to `ContinuousAt CedgeBase x0` plus explicit
  fixed-base edge-matrix measurability.
- The adapted product-difference lower bound is produced by the same local
  self-base product-family theorem, so the local continuity requirement is
  sufficient.
- Source-stratum/residual measurability is not inferred from local continuity;
  it is supplied through the `hEdgeMatrix` hypothesis consumed by the existing
  measurable-edge source-measure theorem.
- Radius handling is unchanged: `Rprod <= Rmax` is obtained first, the
  finite-integral theorem shrinks below `Rprod`, and the final radius is
  bounded by the original `Rmax`.

## Boundary

This theorem does not construct the signed-box source chart, prove the
weighted pushforward identity, prove the residual monomial lower bound,
derive a density/Jacobian factor, produce normal crossings, compute pole
order, or extract an RLCT.
