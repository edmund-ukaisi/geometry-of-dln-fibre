# Review - A4 continuing old-top/source-suffix paper-Cprime stack without chart family

Reviewers: xhigh subagents `Singer` and `Heisenberg`.

Verdict: pass.

## Findings

No blocking findings.

## Source/Reproduction Audit

Singer confirmed that this is a finite A4 bookkeeping cleanup below source
production.  The theorem packages the local Case 2 `Q/P` calculation from
Aoyagi PDF pp. 20-22 after attaching old top source rows and the supplied raw
source suffix.  The chart-family boundary is not doing source work here: the
direct proof can use the corrected new-label certificate, concrete
`case2Succ` recurrence post-data, finite `Q/P` witness, old-top lifting, and
suffix multiplication.

Singer explicitly flagged the necessary caveats: no source production of
`Csucc` or full source-ordered `C'^(S+1)`, no suffix production, no coverage or
transition regularity, no analytic Jacobian data, no normal-crossing
certificate, no pole order, no RLCT extraction, and no printed Case 2 vector
repair.

## Lean/API Audit

Heisenberg confirmed that
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`
has the same conclusion as the older `withCorrectedPostData` theorem but no
`ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  The old API is now a
compatibility wrapper that binds and ignores `chartFamily`, then delegates to
the chart-family-free theorem.

The direct proof uses the intended low-level facts:

```text
correctedCase2NewLabelCertificate_of_prefixBound
pre.case2Succ_case2SuppliedPostData
Case2CorrectedExponentPostData.updateSelected
IntroducedLabelRecurrenceState.case2Gap_of_leastValueGap
exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData
fromBlocks_mul_verticalBlock_eq_of_tail
sourceSuffixProduct
```

Heisenberg also warned not to route this theorem through
`sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData`,
because that theorem has the reindexed formula-level `Csucc` shape rather than
the old-top/source-suffix paper-`C'` stack.  The implemented proof follows the
pre-reindex finite `Q/P` path.
