# Reproduction - Theorem 2 counted-datum terminal-order bridge

Date: 2026-06-22.

Status: finite A5-to-A6 handoff.  This is not a source-backed classifier
theorem.

## Inputs

Use the existing A6 terminal-order wrappers in
`Theorem2TerminalOrderBridge.lean`.  They end with supplied hypotheses

```text
Set.InjOn TC.branchLabel TC.fullBranches
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula.
```

The new A5 bridge proves the second hypothesis from a supplied classifier:

```text
TC.TerminalMinimumCountDatumClassifier
```

via

```text
TC.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier
```

## Calculation

For every existing final-socket theorem whose last input is the raw upper
bound, keep all preceding hypotheses unchanged and replace the raw upper
bound by `classifier`.

The proof is formal transitivity:

```text
classifier
  -> TC.terminalMinimumLabels.card <= data.theorem2OrderFormula
  -> existing raw-bound A6 wrapper
```

For the first finite-exponent boundary this expands to

```text
D.exponentOrder = TC.terminalMinimumLabels.card
TC.terminalMinimumLabels.card = data.theorem2OrderFormula
-------------------------------------------------------
D.exponentOrder = data.theorem2OrderFormula
```

where the equality on the second line is the A5 cardinal squeeze using
supplied branch-label injectivity plus the classifier-derived upper bound.

## Lean Targets

The Lean names use the shorter suffix `_of_classifier` or `_classifier` to
stay under the repository line-length linter.  In all statements,
`classifier` has type `TC.TerminalMinimumCountDatumClassifier`.

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

## Nonclaims

No counted-datum classifier, branch-label injectivity, back-to-label map,
Eq3/Eq4/Eq5 branch coverage, source labels, terminal `tilde t=0`, chart
production, pole order without A0, normal crossings, or RLCT extraction is
constructed.
