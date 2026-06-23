# Review - A4 paper-Cprime lower rows without chart family

Reviewers: xhigh subagents `Poincare` and `Ampere`.

Verdict: pass.

## Findings

No blocking findings.

## Source Frontier Audit

Poincare confirmed that this is a narrow finite directification below source
production.  It removes a vacuous chart-family dependency from the lower-row
paper-`C'` handoff only.  It does not produce a genuine successor following
object `C'^(S+1)` or `Csucc`, and it does not produce suffix data, successor
charts, coverage, transition regularity, coordinate-produced corrected
post-data, analytic Jacobian data, normal crossings, pole order, or RLCT.

Poincare identified the next feasible finite directification as the
formula-level continuing source-current stack, not as source production.  Any
actual source-produced `Csucc`, suffix, or successor atlas theorem needs a new
chart-production invariant first.

## Lean/API Audit

Ampere confirmed that the chart-family-bearing helpers now retain their old
`chartFamily` argument only as compatibility API.  They delegate to the new
chart-family-free constructors:

```text
sourceChartMap_paperCprimeWeightedLowerRows_withoutChartFamily
sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withoutChartFamily
```

Ampere checked that the direct lower-row proof uses the intended dependency
pattern:

```text
correctedCase2NewLabelCertificate_of_prefixBound
pre.case2Succ_case2SuppliedPostData
Case2CorrectedExponentPostData.updateSelected
IntroducedLabelRecurrenceState.case2Gap_of_leastValueGap
exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData
case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
```

The main proof risk Ampere flagged was the final row-level reindexing of the
successor lower-row diagonal.  The landed proof resolves this by projecting
the low-level `Q/P` equality first and then simplifying the projected equality
into paper-facing names; the focused Lean build passed.

## Caveat

The review is a finite algebra/API review.  It does not review, and the Lean
patch does not prove, global chart production, chart coverage, analytic
regularity, normal crossings, pole order, or RLCT extraction.
