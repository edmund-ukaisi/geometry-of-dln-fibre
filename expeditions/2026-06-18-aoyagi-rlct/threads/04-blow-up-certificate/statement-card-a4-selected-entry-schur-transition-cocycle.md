# Statement card - A4 selected-entry Schur transition cocycle

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryNormalizedMap_schurComplement_transition_cocycle`
- `case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_cocycle`
- `case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_cocycle`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_cocycle`

## Claim

On a finite selected-entry triple overlap, the target lower-right Schur entry
used by the selected-pivot `Q/P` calculation is independent of whether target
coordinates are reached directly from the source chart or through a middle
chart.  The hypotheses are that the middle and target normalized coordinates
are nonzero in the source chart.

## Inputs Kept Explicit

- source, middle, and target selected pivots or chart indices;
- source residual coordinates;
- normalized nonzero middle and target denominators;
- target off-pivot row and column indices.

## Not Proved

No analytic transition regularity, no chart coverage, no open-neighbourhood
gluing, no source-displayed all-pivot atlas, no successor residual/following
factor production, no analytic Jacobian/volume theorem, no global normal
crossings, no pole order, and no RLCT extraction.

## Verification

Passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

Independent xhigh review: `review-selected-entry-schur-transition-cocycle-a4.md`.
