# Review - A4 direct Case 2 reindexed next-source product

Reviewer: xhigh subagent `Noether the 3rd`.

Verdict: pass.

## Findings

No blocking findings.

The only issue found was documentation staleness: the reproduction note still
said the Lean target was planned after the theorem had been implemented.  The
status line has been updated.

## Dependency Audit

The direct theorem

```text
sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData
```

has no `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  Its proof uses the
low-level `exists_case2DisplayedQP...of_postData` path plus corrected
post-data, not
`Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`
and not the older chart-family-bearing wrapper.

The compatibility wrapper

```text
sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData
```

keeps the old chart-family-bearing API but delegates to the direct theorem.

## Fidelity Audit

The theorem is faithful to the finite algebra in Aoyagi Case 2: selected-entry
chart, `Q`, `C' = Q^-1 C`, `P`, `D'''`, then same-stage reindexing.  It proves
only a finite product identity and corrected exponent/level/gap post-data.  It
does not assert source production, chart coverage, normal crossings, pole
order, or RLCT extraction.

## Residual Risk

The reviewer did not run Lean/build commands.  Controller verification records
the build status in the statement card.
