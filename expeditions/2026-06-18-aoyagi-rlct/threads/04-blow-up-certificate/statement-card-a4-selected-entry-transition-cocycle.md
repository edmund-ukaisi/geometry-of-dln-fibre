# Statement card - A4 selected-entry transition cocycle

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryNormalizedMap_transition_target_ne_zero_of_source_ne_zero`
- `selectedEntryNormalizedMap_transition_transition_eq_div_of_ne_zero`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero`

## Claim

On a finite selected-entry triple overlap, the two-step transition from source
chart to middle chart to target chart equals the direct transition from source
chart to target chart, as a target chart-point identity.  The hypotheses are
that the middle and target normalized coordinates are nonzero in the source
chart.

## Inputs Kept Explicit

- source, middle, and target chart indices;
- source selected variable `u`;
- source residual coordinates;
- normalized nonzero middle and target denominators.

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

Independent xhigh review: `review-selected-entry-transition-cocycle-a4.md`.
