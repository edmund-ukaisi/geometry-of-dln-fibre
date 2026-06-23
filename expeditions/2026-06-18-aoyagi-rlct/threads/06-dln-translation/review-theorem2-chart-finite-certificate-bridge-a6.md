# Review - Theorem 2 chart finite-certificate bridge

Reviewer: xhigh Lean/API reviewer `Averroes the 2nd`.

Status: passed.

## Verdict

No blocking API issue.  The slice is appropriate as a thin wrapper in
`Theorem2FinalAssembly.lean`, reusing the finite constructor from
`Theorem2FiniteExponentBridge.lean`.

## Accepted Names

```text
AoyagiTheorem2SuppliedChartFinalBoundary.of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le
AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount
```

## Boundary Checks

- Keep `hNC : Cnc.ExtractionHypothesis lambda poleOrder` as an explicit
  assumption.  Do not derive it from `Cnc`.
- State all finite min/order hypotheses over `Cnc.exponentData`; `activePairs`,
  `ratioAt`, and `minCountInChart` are finite-data API, not analytic
  chart-domain facts.
- Use `minCountInChart` only when the supplied count is already for
  global-minimum coordinates.  If source data instead supplies counts at the
  displayed ratio, add a separate ratio-count variant using
  `countInChartAtRatio`.
- The selected-width provenance field is needed to construct the boundary, but
  the direct pair theorem does not rewrite to selected reduced widths.

## Verification

The reviewer compile-checked the proposed signatures through
`lake env lean --stdin`.  Controller closeout must run the focused module and
full build gates.
