# Review - A2 multi-edge residual-product preservation

Date: 2026-06-25.

Scope: finite multi-edge residual-product preservation for raw p.13
product-coordinate edge matrices.

## Verdict

Accepted at the finite multi-edge scope.  The statement proves preservation of
the ordered transformed-Schur residual product, not equality of raw
lower-right blocks and not equality of suffix states.

## Checks

- The residual factor for each edge is chosen as
  `residualBlock Ebase last p`, not as a preselected final residual matrix.
- The middle-edge case uses the exposed tail invariant `B=0`, so the raw
  middle matrix really has transformed edge `[I,0;0,C(p)]`.
- The right endpoint uses the zero upper-right block; the left and middle
  edges use zero lower-left blocks.  These are the only Schur-residual
  simplifications needed.
- The proof does not require `IsUnit Ctop.det`; that hypothesis belongs to
  coordinate-readout or one-edge Schur-residual cleanup, not this multi-edge
  residual-product equality.

## Boundary

This is pointwise finite matrix algebra for chains with at least two edges.
It should not be cited as a product chart, source-neighborhood, continuity,
measure-transport, normal-crossing, pole-order, or RLCT result.
