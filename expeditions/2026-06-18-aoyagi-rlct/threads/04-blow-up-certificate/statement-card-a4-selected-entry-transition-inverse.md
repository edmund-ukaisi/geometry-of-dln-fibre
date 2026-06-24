# Statement card - A4 selected-entry transition inverse

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryNormalizedMap_transition_eq_div_of_target_normalized_ne_zero`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_self`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_self`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero`

## Claim

On a finite selected-entry overlap, target-normalized coordinates are source
normalized coordinates divided by the normalized target coordinate.  Therefore
the reverse transition from target chart back to source chart returns the
original source chart point under the explicit hypothesis `x_q != 0`.

The Case 2 wrappers specialize the same finite chart-point identity to the
residual-block all-pivot certificate.

## Inputs Kept Explicit

- source and target chart indices;
- source selected variable `u`;
- source residual coordinates;
- normalized nonzero target denominator.

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

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The full-library build completes with pre-existing Core/style warnings outside
this slice.  Review:

```text
threads/04-blow-up-certificate/review-selected-entry-transition-inverse-a4.md
```
