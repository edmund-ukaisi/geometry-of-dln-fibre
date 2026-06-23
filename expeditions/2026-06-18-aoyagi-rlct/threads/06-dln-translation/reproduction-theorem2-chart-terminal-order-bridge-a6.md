# Reproduction - Theorem 2 chart terminal-order bridge

Date: 2026-06-23.

Status: reproduced and formalised; independent review pending.

## Purpose

The previous A5/A6 terminal-order handoff routes chart counts and counted
datum classifiers through the older finite-data final socket
`AoyagiTheorem2SuppliedFinalBoundary D ...`.  After the chart-certificate
socket was introduced, this leaves a small API gap: downstream chart
certificates should be able to consume the same A5 terminal-order data without
forgetting the chart spine.

This slice adds chart-certificate variants of the active chart-count and
displayed-ratio count handoffs.

## Pen-And-Paper Calculation

Let

```text
D = Cnc.exponentData
q = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data.
```

Assume the active-ratio certificate

```text
p in D.activePairs,
D.ratioAt p = q,
forall p' in D.activePairs, q <= D.ratioAt p'.
```

Then the existing A0 finite minimum certificate proves

```text
D.exponentMinimum = q.
```

For the chart-count route, assume a chart whose global-minimum count is the
terminal-minimum label count and a uniform chart-count upper bound:

```text
D.minCountInChart c = TC.terminalMinimumLabels.card,
forall c', D.minCountInChart c' <= TC.terminalMinimumLabels.card.
```

The A0 finite maximum certificate gives

```text
D.exponentOrder = TC.terminalMinimumLabels.card.
```

The existing A5 terminal-order bridge, under supplied branch-label injectivity
and the supplied terminal upper bound

```text
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula,
```

then gives

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

Hence the finite exponent formula fields become

```text
D.exponentMinimum = q,
D.exponentOrder = data.theorem2OrderFormula.
```

Those two fields, together with selected-width provenance and the chart-level
extraction hypothesis

```text
Cnc.ExtractionHypothesis lambda poleOrder,
```

construct `AoyagiTheorem2SuppliedChartFinalBoundary`.

For the displayed-ratio count route, replace `minCountInChart` by

```text
D.countInChartAtRatio q c.
```

The active-ratio certificate is used first to identify `D.exponentMinimum`
with `q`; only then are the ratio-specific counts converted to global-minimum
chart counts by the A0 ratio-count API.

For counted-datum classifier variants, replace only the raw terminal upper
bound by

```text
TC.TerminalMinimumCountDatumClassifier.
```

The existing A5 bridge turns this supplied classifier into the displayed
order-formula upper bound.  Supplied branch-label injectivity remains
separate.

## Lean Targets

All names live in
`lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`, inside
`AoyagiLemma5SuppliedTerminalCandidateFamily`.

```text
theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card
theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card
theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_classifier
theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_classifier
lambda_and_poleOrder_eq_of_chart_activePair_chartCount_terminalMinimumLabels_card
lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_terminalMinimumLabels_card
lambda_and_poleOrder_eq_of_chart_activePair_chartCount_classifier
lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_classifier
```

## Boundary

This is finite A5-to-A6 handoff only.  It does not construct the chart
certificate, chart coverage, analytic unit nonvanishing, active-ratio bounds,
chart-count witnesses or upper bounds, ratio-count facts, counted-datum
classifiers, branch-label injectivity, back-to-label maps, Lemma 5 exactness,
normal crossings, pole order without A0, or RLCT extraction.

The next source-moving frontier remains A4/A0 chart/source production, not
additional final-socket wrappers unless they remove a concrete downstream
obstacle.
