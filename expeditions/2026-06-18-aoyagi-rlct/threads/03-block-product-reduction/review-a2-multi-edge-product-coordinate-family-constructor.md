# Review - A2 multi-edge product-coordinate family constructor

Date: 2026-06-25.

Scope: finite fixed-base multi-edge product-coordinate matrix construction
from a Euclidean regular-coordinate vector and a fixed base edge-matrix
family.

## Verdict

Accepted at the pointwise fixed-`Ebase` scope.  The statement proves the
coordinate readout for the constructed fixed-base matrix family and keeps the
residual coordinate equal to the base residual product.

## Checks

- The regular vector stores `Ctop - I`, so the constructor uses `Ctop = I + X`.
- The raw edge matrices use Aoyagi's p.13 signs: right endpoint `-F3`, middle
  zero off-diagonal blocks, and left endpoint `-Ctop F2`.
- The residual factors are the base transformed Schur residual blocks
  `residualBlock Ebase last p`, not arbitrary lower-right blocks and not a
  preselected final residual matrix.
- The final residual readout is the residual product of `Ebase`; the theorem
  uses residual-product preservation rather than claiming equality of suffix
  states.
- The determinant-unit hypothesis belongs to the coordinate-readout layer; the
  residual-product preservation theorem itself does not need it.

## Boundary

This is finite pointwise matrix algebra.  It should not be cited as the
dependent product family `G(x,u)`, parameter-continuity, product chart
construction, source coverage, density/Jacobian transport, normal crossings,
pole order, or RLCT extraction.
