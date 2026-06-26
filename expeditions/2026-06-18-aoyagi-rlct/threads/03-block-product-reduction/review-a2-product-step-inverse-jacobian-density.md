# Review - A2 product-step inverse Jacobian density

Date: 2026-06-26.

Verdict: accepted at the stated scope.

## Checks

- The statement is target-chart local: the base point is a raw-shaped target
  tuple satisfying `det Ctop != 0` and `det A1 != 0`.
- The inverse coordinate map uses `Ctop^{-1}` and `A1^{-1}` only; it does not
  invert the passive residual block `D`.
- The raw preimage is shown to lie in the source determinant chart before the
  source-side forward density theorem is applied.
- The theorem controls `J(toRaw(y))^{-1}`, not the forward source density
  `J(y)`.
- Positivity at the base point justifies the use of real inverse continuity.
- The lower and upper eventual bounds are local consequences of continuity and
  positivity, not global boundedness on the determinant chart.

## Boundary

This is local unit control for the reciprocal Jacobian factor in chart
coordinates.  It does not prove an unweighted change-of-variables theorem,
does not identify or transport the original DLN prior, does not prove source
coverage, and does not construct normal crossings or extract pole order/RLCT.
