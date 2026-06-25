# Review - A2 fixed-base residual-factor family constructor

Date: 2026-06-25.

Reviewers: controller Lean check, with post-recovery source/API scout summaries
from `Wegener` and `Boole`.

## Scope

Reviewed the new fixed-base supplied-factor constructor in
`RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean_residualBlock_eq
paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean_residualProduct_eq_residualFactorProduct
```

and the reproduction note
`reproduction-a2-fixed-base-residual-factor-family-constructor.md`.

## Verdict

Accepted for the stated fixed-base finite boundary.

The theorem is source-shaped: p.13 keeps the singular part as an ordered
product through residual factors, and the Lean constructor realizes an
explicit supplied factor family as the transformed Schur residual blocks of
the raw p.13 edge matrices.  This is stronger than a terminal readout wrapper
because it verifies the block-level compatibility needed by the
`residualFactorProduct` socket.

## Checks

- The right endpoint uses the existing `productCoordinateRightEndpointMatrix`
  with `F3` and `Cfac last`.
- Middle edges use `productCoordinateMiddleMatrix` with exactly `Cfac p`.
- The left endpoint uses `productCoordinateLeftEndpointMatrix F2 Ctop
  (Cfac 0)`.
- The residual-block theorem proves every traversed Schur residual block is
  the supplied factor, not merely that the final product has a desired value.
- The residual-product theorem delegates to
  `residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct`,
  so the product order is the existing decreasing suffix order.
- No selected-entry factor-product identity is asserted.

## Nonclaims

No construction of `Cfac`, no selected-entry factor-product identity, no
residual-index equivalence, no source chart, no source/image equality, no
source-measure transport, no normal crossings, no pole order, and no RLCT.

## Checks Run

Focused checks passed:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
```

`BlowupArithmetic.lean` was checked because an interrupted Case 2 bridge
attempt touched it; the branch now has no `BlowupArithmetic.lean` diff.
