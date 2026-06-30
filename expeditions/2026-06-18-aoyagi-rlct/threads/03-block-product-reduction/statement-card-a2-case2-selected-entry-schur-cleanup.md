# Statement card - A2 Case 2 selected-entry Schur cleanup

Date: 2026-06-29.

## Statement

Aoyagi's displayed Case 2 selected-entry block cleanup is recorded as finite
matrix algebra:

```text
D = u E,
E Q = [[1,0],[c,Z-ca]],
P B E Q = B [[1,0],[0,Z-ca]]
```

with quotient witnesses `b_i = q_i b0` for the weighted left cleanup.  For the
old source block `D = u E`, the selected variable is absorbed into the row
weights `B' = u B_old`; no additional global `u` remains after that
absorption.

Lean names added in this slice:

```text
pivotFirstMatrix_mul_pivotQ_eq_pivotPostQBlock
case2SourceSelectedSubstitutionBlockOfMem_eq_mul_normalized
case2SourceSelectedNormalizedBlockOfMem_mul_pivotQ
case2DisplayedPaperDchart_mul_Q_eq_pivotPostQBlock
```

Existing weighted cleanup theorems used by this statement:

```text
weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock
weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ
weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ
weightedPivotBlockRowOp_mul_oldDiagonal_mul_smul_pivotPreQBlock_mul_pivotQ
```

## Source reference

Aoyagi PDF pp. 19-22 for the displayed Case 2 selected-entry substitution,
the matrices `Q`, `Q^-1`, `P`, and the product calculation.  This card uses
Aoyagi only and is independent of the quiver-based paper.

## Dependencies

- `case2SourceSelectedChartMapOfMem`
- `case2SourceSelectedNormalizedBlockOfMem`
- `case2SourceSelectedNormalizedMatrixOfMem_pivot`
- `pivotFirstMatrix_eq_pivotPreQBlock`
- `pivotPreQBlock_mul_pivotQ`
- `case2DisplayedPaperDpp_eq_pivotPostQBlock`
- Existing weighted pivot-row operation API in `BlowupArithmetic.lean`

## Nonclaims

This is finite selected-entry block algebra only.  It does not prove analytic
atlas coverage, chart-domain regularity, transition regularity, Jacobian or
volume compatibility, source production, branch termination, source-prior
transport, determinant-chart Haar transport, source-rank coverage, normal
crossings, pole order, or RLCT.

The lower-right block `Z - c a` is not asserted here to be the next residual
block without the separate continuing-branch reindexing and size hypotheses.

## Reproduction and review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-case2-selected-entry-schur-cleanup.md
```

Review:

```text
threads/03-block-product-reduction/review-a2-case2-selected-entry-schur-cleanup.md
```

Verdict: PASS by xhigh source/scope reviewer `Ampere the 4th` and xhigh
Lean/API reviewer `Franklin the 4th`.
