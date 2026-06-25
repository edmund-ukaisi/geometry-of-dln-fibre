# Review - A2 regular coordinate-vector block reconstruction

Date: 2026-06-25.

Scope: finite tagged-coordinate repackaging from a regular scalar coordinate
family to the three p.13 regular block matrices.

## Verdict

Pass at the stated finite scope.

The construction is the inverse of the definition of
`AoyagiRegularBlockCoordinateIndex.value`: each tagged summand is assigned to
the corresponding matrix entry, and the proof is a three-case split on the
coordinate tag.  There is no hidden determinant, inverse, sign convention, or
nonempty-index assumption.

## Checks

- The first block is named `ctopMinusIdentityMatrix` because the coordinate
  readout later uses `Ctop - I`, not `Ctop` itself.
- The helper `ctopMatrix` is only `I + ctopMinusIdentityMatrix`; the theorem
  `ctopMatrix_sub_one` records the matrix-extensional identity needed by the
  later edge-matrix constructor.
- The `F2` and `F3` blocks use the same signs as the cleaned coordinate
  readout.  The signed p.13 edge matrices are separate artifacts.
- The Euclidean theorem is only a coercion/readout wrapper for
  `fun c => u c`; it does not impose or prove a norm comparison.

Read-only xhigh checks by Laplace the 5th and Ptolemy the 5th agreed on the
component definitions, the absence of sign changes in the reconstruction, and
the edge cases for empty index types.  Laplace recommended the optional
`Ctop = I + X` wrapper for the next `G(x,u)` slice; Ptolemy warned against any
larger parameterized fixed-base wrapper that would unfold the full coordinate
map.

## Boundary

This artifact supplies the regular blocks for a later `G(x,u)` constructor.
It does not choose residual blocks, assemble edge matrices, prove the raw
edge-pattern hypotheses, prove continuity in `(x,u)`, construct a product
chart, transport measures, produce normal crossings, prove pole order, or
extract RLCT.
