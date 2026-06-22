# Statement Card - A6 Theorem 2 Counted-Datum Terminal-Order Bridge

## Lean File

`lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`

## Claim

The existing A6 terminal-order sockets can consume a supplied
`TC.TerminalMinimumCountDatumClassifier` instead of a raw supplied upper bound

```text
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula.
```

All other inputs remain explicit: selected-width provenance, A0 extraction,
active-ratio certificates, chart-count certificates, chart-order/terminal-label
identifications where applicable, and supplied branch-label injectivity.

## Lean Names

```text
theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_of_classifier
theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier
theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_classifier
theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier

theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card_of_classifier
theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card_of_classifier
theorem2SuppliedFinalBoundary_of_activePair_chartCount_classifier
theorem2SuppliedFinalBoundary_of_activePair_ratioCount_classifier

lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card_of_classifier
lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card_of_classifier
lambda_and_poleOrder_eq_of_activePair_chartCount_classifier
lambda_and_poleOrder_eq_of_activePair_ratioCount_classifier
```

## Proved

Only finite handoff from the supplied A5 counted-datum classifier boundary to
the A6 final sockets.

## Not Proved

No source construction of the classifier or branch-label injectivity, no
back-to-label map, no Eq3/Eq4/Eq5 coverage, no chart production, no pole order
without A0, no normal crossings, and no RLCT extraction.
