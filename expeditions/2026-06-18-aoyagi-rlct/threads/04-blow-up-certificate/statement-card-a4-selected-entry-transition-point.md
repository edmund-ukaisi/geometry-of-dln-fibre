# Statement card - A4 selected-entry transition point

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint`
- `selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`

## Claim

For the finite selected-entry all-pivot chart family, a source chart point can
be transported to a target chart point on the normalized target-coordinate
overlap.  If the target normalized coordinate is nonzero, the target chart map
at the constructed target point equals the source chart map at the original
source point.

The Case 2 wrapper specializes this to the residual-block center indexed by
`case2ResidualBlockPivotEntries n S J`.

## Inputs Kept Explicit

- source and target chart indices;
- the source selected variable `u`;
- source residual coordinates;
- the normalized nonzero target denominator;
- the finite all-pivot residual-block chart enumeration in the Case 2 wrapper.

## Not Proved

No analytic chart coverage, open-neighbourhood gluing, analytic transition
regularity, Jacobian/volume-form theorem, source production of `Csucc`,
source production of `C'^(S+1)`, suffix production, recurrence post-data,
exponent post-data, normal crossings, pole order, or RLCT extraction.

## Verification

Current checks passed:

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

The full-library build completes with pre-existing Core/style warnings outside
this slice.

Independent review:

```text
threads/04-blow-up-certificate/review-selected-entry-transition-point-a4.md
```
