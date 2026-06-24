# Statement card - A4 Case 2 transition supplied-successor reindexed product

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_reindexedNextSourceProduct_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero`

## Claim

On the displayed Case 2 overlap, if the transition-generated displayed target
data are equipped with an explicit `SourceProductionObligation`, then the
displayed reindexed next-source product can be stated simultaneously with:

- the left substitution block rewritten to the original source selected block;
- the right-hand successor following object written as the supplied `Csucc`.

## Inputs Kept Explicit

- displayed overlap nonzero hypothesis;
- displayed supplied chart-family boundary for `targetU = u*d` and
  `targetResidual q = x_q/d`;
- `SourceProductionObligation` for that target data;
- source suffix index family, suffix matrices, `Csucc`, and `Cterm`.

## Proved

Only a finite composition of two existing consumers:

- displayed transition source-substitution of the lower-left block;
- supplied-obligation reindexed product consumer using `ob.Csucc_eq_formula`.

## Assumed

The source-production obligation and all data it packages.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 20-22.

## Deferred

Construction of the obligation, construction/source-production of `Csucc`,
suffix production, successor chart families, coverage, transition regularity,
analytic Jacobian/volume data, global normal crossings, pole order, and RLCT
extraction.

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
threads/04-blow-up-certificate/review-case2-transition-supplied-successor-reindexed-product-a4.md
```
