# Statement card - A4 Case 2 pivot-first following factor

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `<pending Lean commit>`.

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedNormalizedMatrix`
- `DLNFibre.DLN.Aoyagi.case2DisplayedFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2DisplayedNormalizedMatrix_mul_followingFactor`
- `DLNFibre.DLN.Aoyagi.exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights`

## Statement

Lean now packages the source-displayed Case 2 top-left `Q/P` identity with a
residual following factor supplied before pivot-first reindexing. The theorem
reindexes that factor into pivot-first column coordinates using
`case2DisplayedFollowingFactor`, then applies the displayed Case 2
flat-row-weight `Q/P` identity.

## Source role

Aoyagi writes the following-factor update as `C' = Q^{-1} C`. The existing
pivot-first theorem needs `C` already in pivot-first coordinates. This
checkpoint records the finite reindexing that turns a residual following
factor into that pivot-first `C`.

## Proved

- The displayed normalised residual matrix and reindexed following factor are
  named.
- Multiplying the pivot-first displayed residual matrix by the reindexed
  following factor is the same as reindexing the pre-reindexed product.
- Under flat displayed row weights, the displayed Case 2 `Q/P` identity holds
  with the residual following factor supplied before pivot-first reindexing.

## Assumed

- The residual block has already been normalised at the displayed pivot.
- The row weights are already assigned in displayed residual-row coordinates.
- The theorem is local to the displayed top-left Case 2 chart.

## Not proved

- No source-coordinate construction for the whole product.
- No arbitrary selected-entry pivot chart or chart coverage.
- No regularity/Jacobian theorem for the chart.
- No exponent update, transition invariant, termination proof,
  normal-crossing certificate, or RLCT extraction.

## Reproduction and review

- Reproduction artifact:
  `reproduction-case2-pivot-first-following-factor-a4.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
