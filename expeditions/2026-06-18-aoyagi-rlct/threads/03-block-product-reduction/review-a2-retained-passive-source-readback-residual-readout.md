# Review - A2 retained-passive source-readback residual readout

Reviewer: Descartes the 3rd, xhigh

## Verdict

No blockers.

## Checks

The Lean theorem
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct`
states the proved pointwise equality: fixed-base residual block coordinates are
the scalar entries of
`residualFactorProduct (sourceReadback E).C (Fin.last (M + 1)) 0`.

The index convention is correct: vertices are `Fin (M + 2)`, edges are
`Fin (M + 1)`, the source endpoint is `0 : Fin (M + 2)`, and the terminal
endpoint is `Fin.last (M + 1) : Fin (M + 2)`.

The proof uses only the fixed-base residual-product readout and the
source-readback theorem identifying the suffix `D` block with the
retained-passive residual-factor product.  It does not add determinant-chart
membership, source-image, chart, measure, rank, Jacobian, normal-crossing,
pole-order, or RLCT assumptions.

The reproduction and statement card match the Lean result and keep the
nonclaims explicit.

## Verification

The reviewer typechecked the target Lean file from the `lean/` Lake project
root.  The controller also ran focused and full builds separately before this
review artifact was added.
