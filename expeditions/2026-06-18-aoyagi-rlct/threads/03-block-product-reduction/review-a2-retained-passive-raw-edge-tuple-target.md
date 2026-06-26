# Review - A2 retained-passive raw edge tuple target

Date: 2026-06-26.

Reviewer: Bernoulli the 4th, read-only scout.

## Verdict

Pass.  The raw-edge tuple API is sound at the claimed scope: it is block
decomposition/reassembly plus a finite endpoint reorder.  It is appropriate
as the target-coordinate representation following the retained-passive tuple
source map.

## Checks

- The packing formulas are correct, including `M = 0`: the only edge is both
  first and last, so its top-left block goes to `Ctop` and its lower-left
  block goes to `F3`; the passive families are empty.
- The conversion and inverse identities require no determinant, topology, or
  finiteness hypotheses beyond the matrix types.
- The linear equivalence should need only `[Semiring K]`, matching the Lean
  implementation.
- The composed endomap should inherit exactly the hypotheses of
  `topologyTupleEdgeMatrix`, matching the Lean implementation.
- The name and docstring discipline is acceptable as long as this is described
  as raw block readout/reassembly, not as a retained-passive coordinate
  inverse.

## Proof Hazards

The dependent `Fin.cases` and `Fin.snoc` right-inverse proof is the only
notable hazard.  Direct rewriting can miss syntactic matches; the implemented
proof avoids this by naming the top-left and lower-left expressions locally
and then proving the two component equalities before applying
`Matrix.fromBlocks_toBlocks`.

## Nonclaims Checked

The review explicitly rejects attaching any image equality, homeomorphism,
determinant, density, measure, normal-crossing, pole-order, or RLCT claim to
this layer.
