# Review - A2 product-step Jacobian density continuity

Date: 2026-06-26.

Verdict: accepted at the stated scope.

## Checks

- The continuity theorem is local at determinant-chart points; it does not
  claim global continuity on the ambient raw tuple space.
- The proof accounts for both inverse terms appearing in the derivative
  formula: `A1^{-1}` and `(C1 A1)^{-1}`.
- The CLM-valued continuity proof is finite-dimensional: fixed-vector
  continuity is converted to basis-matrix coordinate continuity, then back to
  continuous-linear maps.
- The lower bound uses positivity at the base point and continuity.  The upper
  bound uses the standard `value + 1` neighborhood argument.
- The theorem names and comments keep the forward-density orientation.

## Boundary

This is only local source-side unit control for the forward Jacobian density
in the weighted Haar theorem.  It does not identify or transport the original
DLN prior, does not prove the chart-side inverse-density theorem, does not
prove source coverage, and does not construct normal crossings or extract
pole order/RLCT.
