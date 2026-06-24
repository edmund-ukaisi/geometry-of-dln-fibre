# Statement card - A4 Case 2 displayed Q/P source-substitution continuing handoff

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.case2DisplayedSourceSubstitutionBlock_eq_sourceSelectedSubstitutionBlockOfMem_displayed`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_QP_sourceSubstitution_frontierBoundaryPackages_of_displayed_normalized_ne_zero`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_QP_sourceSubstitution_continuingCertificate_of_displayed_normalized_ne_zero`

## Claim

On the displayed overlap where the source-normalized coordinate
`x_(J+1,J+1)` is nonzero, transition from an arbitrary all-pivot source chart
to the displayed chart `(J+1,J+1)`.  The transition-generated displayed data
carry the existing target-pivot `Q/P` source-substitution package, the
displayed frontier package, and, under `J+2 <= prefixMinNat n (S+1)`, the
displayed continuing reindexed source-chart certificate.

Only the left substituted residual block in the target-pivot `Q/P` identity is
rewritten to the original source selected substitution block.

## Inputs Kept Explicit

- source all-pivot chart index;
- displayed nonzero denominator `x_(J+1,J+1) != 0`;
- source recurrence/exponent/least-value data;
- supplied chart-family boundary for the target-pivot `Q/P` identity;
- following-factor parameter `C`;
- continuing guard for the continuing-certificate theorem.

## Not Proved

The normalized block, Schur block, successor weights, transported following
factor, and displayed continuing certificate remain transition-generated
displayed target data.

This slice does not prove the deeper displayed reindexed next-source product
with the source-side substitution block.  It also proves no analytic
transition regularity, chart coverage, source-displayed all-pivot atlas,
source production of `Csucc` or suffixes, analytic Jacobian/volume theorem,
global normal crossings, pole order, or RLCT extraction.

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
threads/04-blow-up-certificate/review-case2-transition-generated-displayed-qp-source-substitution-continuing-a4.md
```
