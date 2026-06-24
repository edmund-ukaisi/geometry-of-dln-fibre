# Statement card - A4 Case 2 transition source-current stack supplied successor

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero`

## Claim

On the displayed Case 2 overlap, if the transition-generated displayed target
data are equipped with a supplied `SourceProductionObligation`, then the
continuing source-current stack package can be stated simultaneously with:

- the displayed target chart-map value equal to the original source chart-map
  value;
- the displayed target substitution block rewritten to the original source
  selected substitution block;
- the right-hand successor following object written as the supplied `Csucc`.

## Inputs Kept Explicit

- displayed overlap nonzero hypothesis;
- target displayed data `targetU = u*d` and `targetResidual q = x_q/d`;
- continuing guard `J+2 <= prefixMinNat n (S+1)`;
- displayed supplied boundary `data` for `targetU`;
- `SourceProductionObligation data targetResidual ... C Ctail Csucc Cterm`;
- source suffix index family, suffix matrices, `Csucc`, and `Cterm`.

## Proved

Only a finite composition of:

- displayed transition chart-map equality;
- displayed transition substitution-block equality;
- the supplied-obligation source-current stack consumer with supplied
  substitution block and supplied `Csucc`.

## Assumed

The source-production obligation and all data it packages, including `Csucc`,
`Cterm`, suffix data, and the formula equalities inside the obligation.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 20-22.

## Deferred

Construction of the obligation, construction/source-production of `Csucc`,
source suffix production, successor chart families, coverage, transition
regularity, analytic Jacobian/volume data, global normal crossings, pole
order, termination, and RLCT extraction.

## Verification

Controller gates passed on 2026-06-24:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry gate reported zero `sorry`, zero `#exit`, zero `native_decide`,
and zero `axiom`.

Independent review artifact:

```text
threads/04-blow-up-certificate/review-case2-transition-source-current-stack-supplied-successor-a4.md
```
