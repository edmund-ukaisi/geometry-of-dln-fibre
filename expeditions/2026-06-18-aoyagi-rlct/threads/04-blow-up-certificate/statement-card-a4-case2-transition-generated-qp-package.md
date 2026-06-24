# Statement card - A4 Case 2 transition-generated Q/P package

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_package_of_target_normalized_ne_zero`

## Claim

For a Case 2 all-pivot selected-entry source-to-target transition point on the
normalized target-coordinate overlap, the transition-generated target chart
data simultaneously satisfy:

- finite chart-map equality with the original source chart point;
- the existing supplied target-pivot source-selected `Q/P` identity;
- the denominator-cleared target lower-right Schur formula.

## Inputs Kept Explicit

- source and target chart indices;
- source selected variable `u` and source residual coordinates;
- normalized nonzero target denominator;
- supplied recurrence/exponent/chart-family boundary data used by the existing
  source-selected `Q/P` theorem;
- following-factor parameter `C`.

## Not Proved

No analytic transition regularity, no chart coverage, no open-neighbourhood
gluing, no source-displayed all-pivot atlas, no chart-produced recurrence or
exponent post-data, no successor residual/following factor production, no
analytic Jacobian/volume theorem, no global normal crossings, no pole order,
and no RLCT extraction.

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

- `review-case2-transition-generated-qp-package-a4.md`

The full `DLNFibre` build completed with pre-existing Core/style warnings
outside this slice.
