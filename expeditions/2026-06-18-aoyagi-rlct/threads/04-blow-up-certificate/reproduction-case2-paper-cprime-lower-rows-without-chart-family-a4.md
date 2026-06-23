# Pen-and-paper reproduction - A4 paper-Cprime lower rows without chart family

Status: reproduced, formalised, and xhigh-reviewed.

Review: `review-case2-paper-cprime-lower-rows-without-chart-family-a4.md`.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  The displayed top-left chart introduces
`C' = Q^-1 C`, applies the displayed `Q/P` row operation, and then reads the
post-pivot lower rows as the next same-stage following product.

This note records only the finite lower-row paper-`C'` handoff.  It does not
construct the full successor matrix `C'^(S+1)`, a successor chart family, or
source-produced transition data.

## Existing Calculation

The earlier paper-`C'` handoff proved that, for a row-operation witness `q`,

```text
lowerRows(
  P_q * (diag(pre weights) * source substitution block) * source following C
)
 =
diag(successor lower-row weights)
  * post-pivot residual block
  * source following factor at (S,J+1).
```

The proof has three finite ingredients:

1. the displayed `Q/P` identity;
2. lower-row projection of `diag(b') D''' C'`;
3. the lower-tail identity saying the post-pivot free rows of
   `Q^-1 C` are the next same-stage source following factor.

The older proof routed through
`of_sourceChartMap_case2Succ_updateSelected`, and hence carried a
`Case2ResidualBlockChartFamilyBoundary` argument, but that boundary was not
used to produce chart coverage or transition regularity in this lower-row
calculation.

## Direct Finite Proof

Let

```text
upivot = case2DisplayedSourceChartMap n hS hcont u residual (J+1,J+1),
post   = pre.case2Succ upivot.
```

The direct proof rebuilds the data from finite constructors:

```text
correctedCase2NewLabelCertificate_of_prefixBound
pre.case2Succ_case2SuppliedPostData upivot
Case2CorrectedExponentPostData.updateSelected
IntroducedLabelRecurrenceState.case2Gap_of_leastValueGap
```

The displayed source substitution identity is obtained directly from

```text
exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData
```

with `case2SourceResidualBlock residual` and `case2SourceFollowingFactor C`.
After projecting this equality to the lower rows, the proof rewrites the
paper-facing names `D'''` and `C' = Q^-1 C`, then applies

```text
case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
case2DisplayedPostPivotFreeFollowingFactor_paperCprime_eq_sourceFollowingFactor_succ
```

The corrected exponent, level, least-value-gap, and recurrence-gap outputs
are the same concrete post-data projections used in the recent
chart-family-free Case 2 certificate constructors.

The arbitrary following-product variant is then only congruence: multiply the
proved lower-row equality on the right by the supplied matrix `F`.

## Lean Targets

```text
sourceChartMap_paperCprimeWeightedLowerRows_withoutChartFamily
sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withoutChartFamily
```

The older APIs

```text
sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData
sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData
```

remain compatibility wrappers that ignore their old chart-family arguments.

## Boundary Checks

- The equality is lower-row only; the pivot row is not part of the conclusion.
- The successor lower-row diagonal stays explicit.
- `C' = Q^-1 C` is Aoyagi's displayed transported paper factor, not a
  source-produced full successor `C'^(S+1)`.
- The arbitrary right factor `F` remains supplied.
- No source production of `Csucc`, suffix production, successor chart-family
  construction, coverage or transition regularity, analytic Jacobian or
  volume-form theorem, normal crossings, pole order, RLCT, or repair of the
  printed Case 2 vector mismatch is claimed.

## Kill Conditions

- Kill the slice if the direct constructors take `ChartRegular`,
  `TransitionRegular`, or `Case2ResidualBlockChartFamilyBoundary`.
- Kill the slice if the direct proof calls
  `of_sourceChartMap_case2Succ_updateSelected`.
- Do not rename these theorems as successor production, source production, or
  a normal-crossing certificate.
