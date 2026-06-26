# Statement Card - A2 retained-passive source right inverse

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_lowerLeftBlock_L_of_L_eq_lowerUnitriangular
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_lowerLeftBlock_L_of_exists_L_eq_lowerUnitriangular
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.retainedPassiveSolvedA3_last_eq_of_productTailSum_eq
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.retainedPassiveSolvedA3_last_eq_of_productTailSum_eq_of_ne_last
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_solvedA1_residualFactorProduct_eq_Ctop
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_D_eq_residualFactorProduct_C
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_lowerLeftBlock_L_eq_lowerLeftProductTailSum
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_solvedA3_eq_lowerLeftBlock
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.retainedPassiveTransformedEdge_sourceReadback_eq_sourceReadbackTransformedEdge
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart
```

## Reproduction

```text
reproduction-a2-retained-passive-source-right-inverse.md
```

## Claim

For any retained-passive-shaped source edge family satisfying
`sourceRecursiveDetChart`, the explicit source readback is a right inverse:

```text
(sourceReadback E).edgeMatrix = E.
```

Equivalently, every edge family in the recursive determinant chart is realised
by the retained-passive nonredundant coordinate source map.

## Method

The proof is finite suffix-state algebra.  The source-readback solved `A1`
products recover suffix `Ctop` blocks, and the stored Schur residuals recover
suffix `D` products.  A lower-unitriangular one-step recurrence identifies the
suffix `L` lower-left block with the explicit retained-passive lower-left tail
sum.  At `i = 0`, this makes the full actual lower-left tail equal to the
readback field `F3`.

The final solved `A3` component is then forced by splitting that tail into
early and final contributions and cancelling `CtopLast^-1 * CtopLast`.  All
non-final `A3` components are seed projections.  With solved `A1`, solved
`A3`, `F2`, and `C` identified with the Schur readbacks of the transformed
source edge, `fromBlocks_schurReadbacks_eq` reassembles the transformed edge.
The stored `F2full = -S.B` identity cancels the deterministic
upper-unitriangular multiplier and recovers `E p`.

## Role

This closes the finite two-sided readback algebra on the explicit recursive
determinant source chart, together with the prior left-inverse theorem
`sourceReadback_edgeMatrix_eq` on retained-passive determinant-chart
coordinates.  It prepares, but does not yet state, a local inverse or
homeomorphism theorem.

## Nonclaims

No openness of the recursive determinant chart, equality with the whole source
image, local homeomorphism, source-rank coverage, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT extraction is
proved.

## Verification

Focused and topology checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

Full-library and hygiene checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

Review:
`review-a2-retained-passive-source-right-inverse.md`.
