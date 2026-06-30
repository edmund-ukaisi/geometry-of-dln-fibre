# Review - A2 Case 2 selected-entry Schur cleanup

Date: 2026-06-29.

## Source and scope review

Reviewer: Ampere the 4th, xhigh source/scope review.

Verdict: PASS.

The reviewer checked Aoyagi PDF pp. 19-22 against the reproduction,
statement card, and Lean wrapper statements.  The finite algebra matches the
paper's displayed Case 2 calculation:

```text
D = u E,
E Q = [[1,0],[c,Z-ca]],
P B E Q = B [[1,0],[0,Z-ca]]
```

with the selected variable `u` absorbed into the post-substitution row weights
and no second global `u`.  The reviewer found no overclaim of analytic atlas
coverage, source production, source-prior transport, normal crossings, pole
order, RLCT, or next residual-block production without continuation
hypotheses.

## Lean and API review

Reviewer: Franklin the 4th, xhigh Lean/API review.

Verdict: PASS.

The reviewer checked:

```text
pivotFirstMatrix_mul_pivotQ_eq_pivotPostQBlock
case2SourceSelectedSubstitutionBlockOfMem_eq_mul_normalized
case2SourceSelectedNormalizedBlockOfMem_mul_pivotQ
case2DisplayedPaperDchart_mul_Q_eq_pivotPostQBlock
```

and the nearby weighted cleanup API around
`weightedPivotBlockRowOp_mul_oldDiagonal_mul_smul_pivotPreQBlock_mul_pivotQ`.
Names match the statements, docstrings stay at finite algebra and notation
claims, and the wrappers reuse the existing pivot and weighted APIs rather
than duplicating fragile algebra.

## Verification

Local Lean builds were used for this slice, per operator instruction.

Passed:

```text
cd lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
env LEAN_NUM_THREADS=3 lake build DLNFibre
scripts/sorries
git diff --check
rg -n 'sorry|axiom|native_decide|#exit|admit' <touched Aoyagi Lean files>
```

The full build reports pre-existing warnings in unrelated modules, but no
errors.  The forbidden-marker scan has no matches after changing four old
doc-comment uses of the English word `admit` to `give`.

## Nonclaims

This review accepts only finite selected-entry block algebra.  It proves no
analytic atlas coverage, chart-domain regularity, transition regularity,
Jacobian or volume compatibility, source production, branch termination,
source-prior transport, determinant-chart Haar transport, source-rank
coverage, normal crossings, pole order, or RLCT.
