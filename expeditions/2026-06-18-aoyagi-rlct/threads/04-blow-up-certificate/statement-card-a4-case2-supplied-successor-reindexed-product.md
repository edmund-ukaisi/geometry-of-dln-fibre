# Statement card - A4 Case 2 supplied-successor reindexed product

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `Case2DisplayedReindexedNextSourceProductEqWithSubstitutionBlockAndCsucc`
- `sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData_of_substitutionBlock_eq_of_Csucc_eq`
- `SourceProductionObligation.reindexedNextSourceProduct_of_substitutionBlock_eq`

## Claim

The displayed Case 2 reindexed next-source product can be restated with a
supplied successor following object `Csucc`, provided the theorem also receives
the explicit equality

```text
Csucc =
  case2DisplayedSourceSuccessorFollowingFactor n hS hcont residual C.
```

The row-operation witness and all corrected post-data are the ones already
obtained from the displayed reindexed product theorem.  The
`SourceProductionObligation` wrapper is just this same theorem with
`hCsucc := ob.Csucc_eq_formula`.

## Inputs Kept Explicit

- the supplied substitution-block equality
  `case2DisplayedSourceSubstitutionBlock ... = B`;
- the supplied successor equality
  `Csucc = case2DisplayedSourceSuccessorFollowingFactor ... C`;
- source recurrence, exponent, level, and least-value-gap data;
- the continuation and stage hypotheses.

## Proved

Only finite congruence: substitute the explicit `Csucc` equality into the
right-hand side of the already-proved displayed reindexed product identity.

## Assumed

The supplied object `Csucc` and its equality to the formula-level successor
following factor.

## Cited

None in Lean.  The source motivation is Aoyagi PDF pp. 20-22, but this Lean
slice is finite matrix bookkeeping.

## Deferred

Construction of `Csucc`, suffix/following-product source production,
successor chart families, coverage, transition regularity, analytic
Jacobian/volume data, global normal crossings, pole order, and RLCT
extraction.

## Verification

Controller gates passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
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
threads/04-blow-up-certificate/review-case2-supplied-successor-reindexed-product-a4.md
```
