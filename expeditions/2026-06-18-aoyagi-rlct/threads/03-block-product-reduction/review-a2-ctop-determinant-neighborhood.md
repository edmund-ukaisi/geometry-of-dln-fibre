# Review - A2 Ctop determinant neighborhood

Date: 2026-06-25.

Scope: elementary determinant neighborhood for the regular-coordinate block
`Ctop(u) = I + X(u)`.

## Verdict

Accepted at the determinant-chart scope.  The proof supplies the explicit
`IsUnit(det(Ctop(u)))` hypothesis needed by the pointwise p.13
product-coordinate constructor for all sufficiently small Euclidean regular
coordinates.

## Checks

- The stored first coordinate block is `Ctop - 1`, so the reconstructed matrix
  is `Ctop(u) = I + X(u)`.
- At `u = 0`, the first coordinate block is zero and `Ctop(0) = I`; the
  determinant is `1`.
- The empty-`ι` case is harmless: the empty identity determinant is still `1`.
- The proof uses only continuity of coordinate projections, continuity of the
  determinant, and openness of the real unit locus.
- The `μ` and `ν` indices do not affect the determinant, but they are needed
  to give the full regular-coordinate space a finite Euclidean metric for the
  ball version.
- The p.13 signs in the `F2` and `F3` edge blocks do not enter this
  determinant calculation.

## Boundary

This theorem only removes the determinant-unit hypothesis locally near
`u = 0`.  It should not be used as a continuity theorem for `CedgeProd(x,u)`,
a source-coverage theorem, a rank-stratum theorem, a measure-transport
theorem, a normal-crossing certificate, a pole-order theorem, or an RLCT
extraction.
