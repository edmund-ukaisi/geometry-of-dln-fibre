# Statement card - A6 Theorem 2 chart terminal-order bridge

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_classifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_classifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_chartCount_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_chartCount_classifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_classifier`

## Claim

The chart-certificate final boundary can consume the existing A5 terminal-order
and counted-datum classifier handoffs without forgetting the chart certificate.

## Proved

Given selected-width provenance, the chart-level A0 extraction hypothesis, an
active-ratio minimum certificate, chart-count or displayed-ratio chart-count
data equal to `TC.terminalMinimumLabels.card`, a uniform all-chart upper bound
by `TC.terminalMinimumLabels.card`, supplied branch-label injectivity, and
either a supplied terminal upper bound or a supplied
`TerminalMinimumCountDatumClassifier`, Lean constructs
`AoyagiTheorem2SuppliedChartFinalBoundary`.

The pair-form wrappers derive the displayed Theorem 2 lambda formula and
order formula for `lambda` and `poleOrder`.

## Not Proved

No chart certificate, chart coverage, analytic unit nonvanishing, source
active-ratio inequality, source chart-count fact, counted-datum classifier,
branch-label injectivity, back-to-label map, Lemma 5 exactness, pole order
without A0, normal crossings, or RLCT extraction is proved.

## Verification

Focused target:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
```

Full closeout should also run:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderBridge
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

Independent xhigh review passed:
`review-theorem2-chart-terminal-order-bridge-a6.md`.
