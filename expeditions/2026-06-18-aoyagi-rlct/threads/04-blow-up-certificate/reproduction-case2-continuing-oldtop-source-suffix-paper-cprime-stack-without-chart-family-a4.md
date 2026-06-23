# Pen-and-paper reproduction - A4 continuing old-top/source-suffix paper-Cprime stack without chart family

Status: reproduced, formalised, and xhigh-reviewed.

Review: `review-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The continuing displayed top-left chart forms
the transported paper following factor `C' = Q^-1 C`, keeps the old top source
rows, and then continues the product with the remaining source suffix
`prod_{s=S+2}^L C^(s)`.

This note records only the finite old-top/source-suffix stack identity for the
continuing branch.  It does not produce a successor source object, a source
suffix, or chart-transition data.

## Dependency Audit

The existing stack theorem packages:

- nonemptiness of the next residual-block center under `J+2 <= M(S+1)`;
- a finite matrix identity with old source rows, the displayed pivot-first
  residual block, paper `C' = Q^-1 C`, and the supplied raw suffix product;
- corrected exponent post-data for the new label `(S,J+1)`;
- successor level invariants, least-value gap, and recurrence Case 2 gap;
- finite selected-entry center membership, divisibility, and
  principalization by `u`.

None of these fields need chart regularity or transition regularity.  The old
proof asked for `Case2ResidualBlockChartFamilyBoundary` because it routed
through the supplied displayed chart-family boundary constructor
`of_sourceChartMap_case2Succ_updateSelected`, then used only its finite
`Q/P` and corrected post-data projections.

## Direct Finite Proof

Let

```text
upivot = case2DisplayedSourceChartMap n hS hcont u residual (J+1,J+1),
post   = pre.case2Succ upivot.
```

The direct proof constructs the same data from finite ingredients:

```text
correctedCase2NewLabelCertificate_of_prefixBound
pre.case2Succ_case2SuppliedPostData upivot
Case2CorrectedExponentPostData.updateSelected
IntroducedLabelRecurrenceState.case2Gap_of_leastValueGap
```

The displayed `Q/P` identity is obtained directly from the corrected new-label
certificate and the concrete `case2Succ` post-data:

```text
exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData
```

This gives the lower residual-tail equality.  The old top rows are attached by

```text
fromBlocks_mul_verticalBlock_eq_of_tail
```

and the supplied raw suffix product is attached by congruence:

```text
congrArg (fun M => M * sourceSuffixProduct κ Ctail S hSuffix)
```

The corrected exponent, level, least-value-gap, and recurrence-gap fields are
the same concrete post-data projections used in the chart-family-free
reindexed product theorem.

## Lean Target

```text
sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily
```

The older theorem

```text
sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData
```

is retained as a compatibility wrapper that ignores its old chart-family
argument and delegates to the chart-family-free theorem.

## Boundary Checks

- The suffix `sourceSuffixProduct κ Ctail S hSuffix` remains supplied.
- The theorem uses paper `C' = Q^-1 C` in the old-top/source-suffix stack; it
  is not the source-produced successor `C'^(S+1)`.
- No `Csucc`, successor chart family, suffix, coverage, transition regularity,
  analytic Jacobian/volume-form theorem, normal crossings certificate, pole
  order, or RLCT is produced.
- The corrected Case 2 post-data remains the earlier prefix-minimum repair; no
  source theorem repairing Aoyagi's printed Case 2 vector is claimed.

## Kill Conditions

- Kill the slice if the direct constructor takes `ChartRegular`,
  `TransitionRegular`, or `Case2ResidualBlockChartFamilyBoundary`.
- Kill the slice if the direct proof calls
  `of_sourceChartMap_case2Succ_updateSelected` or depends on a trivial chart
  regularity witness.
- Do not rename the theorem as source production, successor production, or an
  A0 normal-crossing certificate.
