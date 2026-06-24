# Statement card - A4 Case 2 displayed reindexed product source-substitution

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `Case2DisplayedReindexedNextSourceProductEqWithSubstitutionBlock`
- `sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData_of_substitutionBlock_eq`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.case2DisplayedSourceSubstitutionBlock_transition_eq_sourceSelectedSubstitutionBlockOfMem_of_displayed_normalized_ne_zero`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_reindexedNextSourceProduct_sourceSubstitution_of_displayed_normalized_ne_zero`

## Claim

On the displayed overlap where the source-normalized coordinate
`x_(J+1,J+1)` is nonzero, transition an arbitrary all-pivot source chart to
the displayed chart `(J+1,J+1)` and apply the already-proved displayed
reindexed next-source product to the transition-generated displayed data.

The new wrapper rewrites only the left substitution block in that product:

```text
DisplayedSub(targetU,targetResidual) = Sub_p(u,residual),
```

where `targetU = u*d`, `targetResidual q = x_q/d`, and
`d = x_(J+1,J+1)`.

## Inputs Kept Explicit

- source all-pivot chart index;
- displayed nonzero denominator `x_(J+1,J+1) != 0`;
- source recurrence, exponent, level, and least-value-gap data;
- following-factor parameter `C`;
- transition-generated displayed residual data.

## Not Proved

The right-hand side of the reindexed product remains displayed
transition-generated data.  In particular, the post state is
`pre.case2Succ targetU`, the post-pivot residual block uses the displayed
transition residuals, and the successor following factor is still the
formula-level `case2DisplayedSourceSuccessorFollowingFactor targetResidual C`.

This does not source-produce `Csucc`, suffixes, successor charts, or a
source-facing successor residual block.  It also proves no analytic transition
regularity, chart coverage, analytic Jacobian/volume theorem, global normal
crossings, pole order, or RLCT extraction.

## Verification

Controller gates passed:

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

Independent review artifact:

```text
threads/04-blow-up-certificate/review-case2-displayed-reindexed-product-source-substitution-a4.md
```
