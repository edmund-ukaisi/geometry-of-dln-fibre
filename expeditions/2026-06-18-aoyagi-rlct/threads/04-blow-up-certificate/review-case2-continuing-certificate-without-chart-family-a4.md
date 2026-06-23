# Review - A4 continuing certificate without chart family

Reviewer: xhigh subagent `Copernicus`.

Verdict: pass.

## Findings

No blocking findings.

## Dependency Audit

The three direct constructors

```text
sourceChartMap_continuingReindexedSourceChartCertificate_withoutChartFamily
sourceChartMap_continuingReindexedSourceChartUnitCertificate_withoutChartFamily
sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily
```

have no `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  The base constructor calls
the chart-family-free reindexed product theorem
`sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData`.
The review found no use of
`Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`
or trivial chart-family witnesses in this new path.

The old chart-family-bearing constructors remain compatibility wrappers only:
they bind the old `chartFamily` argument and delegate to the corresponding
`_withoutChartFamily` theorem.

## Fidelity Audit

The docs and comments frame the result as finite continuing Case 2 certificate
packaging only.  They explicitly exclude source production of `Csucc`, suffix
production, chart coverage, normal crossings, pole order, and RLCT extraction.

## Residual Risk

The reviewer did not run Lean build commands.  Controller verification records
the build status in the statement card.
