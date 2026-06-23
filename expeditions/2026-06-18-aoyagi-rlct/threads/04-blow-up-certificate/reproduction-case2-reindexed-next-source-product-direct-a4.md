# Pen-and-paper reproduction - A4 direct Case 2 reindexed next-source product

Status: reproduced, formalised, and xhigh-reviewed.

Review: `review-case2-reindexed-next-source-product-direct-a4.md`.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The displayed top-left chart uses

```text
a'_(J+1,J+1) = u,
a'_(i,j) = u a_(i,j)  for the remaining residual-block entries,
```

then forms the regular row/column operations `P`, `Q`, and `Q^-1`, and writes
the transported following factor as `C' = Q^-1 C`.  In the continuing branch,
the paper reads the resulting product as the next same-stage source product
for `(S,J+1)`.

This note isolates the finite algebra that does not need a chart-family
regularity boundary.

## Direct Dependency Chain

The old theorem

```text
sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData
```

obtained the displayed source-chart `Q/P` identity through
`Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`.
That boundary also carried a `Case2ResidualBlockChartFamilyBoundary`, whose
current witnesses may be the trivial `True` predicates.  The matrix identity
itself does not use chart regularity.

The direct proof uses only the following finite ingredients:

1. The continuation bounds `1 <= S`, `S <= L`, and
   `J+1 <= prefixMinNat n (S+1)` produce the corrected new-label certificate.
2. The old level/least-value bridge and integer Case 2 least-value gap give
   the recurrence gap `pre.case2Gap`.
3. The concrete successor `pre.case2Succ upivot`, where
   `upivot = sourceChartMap(J+1,J+1)`, supplies the recurrence post-data:
   old labels are unchanged and the new label has level `J` and variable
   `upivot`.
4. The corrected selected-label overrides supply the exponent post-data.
5. The low-level theorem
   `exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData`
   gives the displayed lower-block `Q/P` identity with successor weights.
6. `fromBlocks_mul_verticalBlock_eq_of_tail` lifts that lower-block identity
   across the unchanged old top rows.
7. `case2DisplayedPivotFirstRHS_reindex_nextSourceProduct` reindexes the
   pivot-first right-hand side to the next same-stage source product.

Thus the chart-family boundary is not a mathematical input for this theorem.

## Product Calculation

Let

```text
row = displayed pivot row,
col = displayed pivot column,
A = displayed D chart,
upivot = sourceChartMap(J+1,J+1),
post = pre.case2Succ(upivot),
Csucc(j,a) =
  if j = J+1 then top row of Q^-1 C at a
  else C(j,a).
```

The low-level `Q/P` theorem supplies a row operation `q` such that

```text
lowerLeft * sourceFollowing(C)
  = lowerRight * paperCprime(C),
```

where `lowerLeft` is the source-chart substituted lower block with old row
weights, and `lowerRight` is the weighted `D'''` block with the corrected
successor row weights.  Lifting by old top rows gives

```text
[oldTopWeight  0; 0 lowerLeft] * [oldTop(C); sourceFollowing(C)]
  =
[oldTopWeight  0; 0 lowerRight] * [oldTop(C); paperCprime(C)].
```

The right side is the pivot-first form already reindexed in the previous
source-product calculation:

```text
[oldTopWeight  0; 0 lowerRight] * [oldTop(C); paperCprime(C)]
  =
[post oldTopWeight 0; 0 post residual weight * post residual block]
  * [oldTop_{J+1}(Csucc); sourceFollowing_{S,J+1}(Csucc)].
```

Composing the two equalities gives the direct next-source-product identity.

## Post-Data Calculation

The same direct inputs produce the fields formerly projected from the supplied
boundary:

```text
exponentPost =
  exponentPre.extendDomain_correctedCase2NewLabel_of_postData
    correctedNewLabel
    Case2CorrectedExponentPostData.updateSelected

postLevelInvariants =
  case2Succ_case2SuppliedPostData.levelInvariants_of_correctedExponentPostData

successorLeastValueGap =
  case2IntroducedLabelLeastValueGap_succ

postCase2Gap =
  case2Succ_case2SuppliedPostData.case2Gap_of_leastValueGap_of_correctedExponentPostData
```

No chart regularity or transition regularity appears in these computations.

## Lean Target

```text
sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData
```

The existing chart-family-bearing theorem should remain as a compatibility
wrapper, but its proof should delegate to the direct theorem.

## Boundary Checks

- This proves a finite product/post-data theorem only.
- It does not construct `Csucc` as source-produced chart data; `Csucc` is the
  formula-level displayed successor following factor.
- It does not construct a successor chart family, suffix, coverage proof,
  transition regularity, analytic Jacobian/volume-form theorem, normal
  crossings, pole order, or RLCT extraction.
- It does not repair the printed Case 2 vector; it uses the corrected
  prefix-minimum new-label certificate already isolated in Lean.
- It does not identify transported terminal rows with original rows outside
  the actual-width column-exhausted branch.

## Kill Conditions

- The proof must not call
  `Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`
  or the old chart-family-bearing theorem.
- The statement must not have `ChartRegular`, `TransitionRegular`, or
  `Case2ResidualBlockChartFamilyBoundary` arguments.
- The result must not be described as full source production of Aoyagi's
  successor chart object.
