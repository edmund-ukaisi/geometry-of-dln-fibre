# Statement card - A4 Case 2 source-current stack substitution block

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc_of_substitutionBlock_eq`

## Claim

The continuing source-current stack consumer for a supplied successor `Csucc`
can be restated with a supplied lower-left substitution block `B`, provided
the explicit equality

```text
case2DisplayedSourceSubstitutionBlock n data.stage_pos data.continuation
  u residual = B
```

is supplied.

## Inputs Kept Explicit

- source-production obligation `ob`;
- continuing guard `J+2 <= prefixMinNat n (S+1)`;
- suffix family and suffix matrices already required by `ob`;
- supplied block `B` and equality `hB`.

## Proved

Only finite congruence in the existing source-current stack matrix identity.

## Assumed

The source-production obligation, supplied successor object `Csucc`, supplied
suffix data, and supplied block equality.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 20-22.

## Deferred

Construction of `ob`, source-production of `Csucc`, suffix production,
successor chart construction, transition regularity, chart coverage, analytic
Jacobian/volume data, global normal crossings, pole order, and RLCT
extraction.

## Verification

Controller gates passed on 2026-06-24:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry gate reported zero `sorry`, zero `#exit`, zero `native_decide`,
and zero `axiom`.

Independent review artifact:

```text
threads/04-blow-up-certificate/review-case2-source-current-stack-substitution-block-a4.md
```
