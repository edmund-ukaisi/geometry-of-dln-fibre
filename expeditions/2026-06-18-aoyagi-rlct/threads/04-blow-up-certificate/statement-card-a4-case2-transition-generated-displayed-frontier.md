# Statement card - A4 Case 2 transition-generated displayed frontier

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.displayedChartIndex`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finsetSubtypeChartEquiv_displayedChartIndex`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_frontierBoundaryPackages_of_displayed_normalized_ne_zero`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingCertificate_of_displayed_normalized_ne_zero`

## Claim

On the overlap where the displayed normalized coordinate is nonzero, any
all-pivot Case 2 selected-entry source chart can be transitioned to the
displayed top-left chart.  The transition-generated displayed data have the
same finite chart map as the original source point and satisfy the existing
displayed source-chart frontier package.  Under the continuing guard, they
also satisfy the displayed continuing reindexed source-chart certificate.

## Inputs Kept Explicit

- source all-pivot chart index;
- source selected variable `u` and residual coordinates;
- nonzero displayed normalized coordinate;
- source recurrence/exponent/least-value data;
- continuing guard for the continuing-certificate theorem;
- following-factor parameter `C` for the continuing certificate.

## Not Proved

No analytic transition regularity, no chart coverage, no open-neighbourhood
gluing, no source-displayed all-pivot atlas, no source production of a global
successor object or suffixes, no analytic Jacobian/volume theorem, no global
normal crossings, no pole order, and no RLCT extraction.

This is not the separate substitution-block rewrite saying the
transition-generated displayed substitution block equals the source-side
selected-entry substitution block.

## Verification

Passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Review artifact:

- `review-case2-transition-generated-displayed-frontier-a4.md`

The full `DLNFibre` build completed with pre-existing Core/style warnings
outside this slice.
