# Review - A2 single-edge product-coordinate family constructor

Date: 2026-06-25.

Scope: finite single-edge product-coordinate matrix construction and
fixed-base coordinate readout.

## Verdict

Accepted at the finite one-edge scope.  Lean proves the residual-coordinate
matrix reconstruction, the explicit one-edge fixed-base product-coordinate
matrix constructor from a Euclidean regular vector `u` and residual matrix
`D`, and the full cleaned product-difference coordinate readout.

## Checks

- The regular coordinate vector stores `Ctop - I`, not `Ctop`; therefore the
  constructor uses `Ctop = I + X`.
- No signs are inserted into the coordinate-vector projections.  The signs
  occur only in the p.13 edge matrix and are removed by the fixed-base suffix
  readout.
- The residual matrix `D` is supplied directly in this slice.  Choosing it
  from a base family is a separate one-edge wrapper; the multi-edge case
  requires residual-factor bookkeeping.

## Boundary

This slice is finite and pointwise.  It should not be used to claim multi-edge
product-coordinate construction, source-chart coverage, continuity in a
source variable, density/Jacobian transport, normal crossings, pole order, or
RLCT.
