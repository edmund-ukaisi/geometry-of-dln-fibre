# Statement card - A6 Theorem 2 chart ratio-count bridge

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary.of_activePair_ratioAt_eq_of_forall_le_of_countInChartAtRatio_eq_of_forall_le`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_ratioCount`

## Claim

The chart final boundary can be built from chart counts stated at the
displayed candidate lambda ratio, provided an active-ratio minimum certificate
first proves that this displayed ratio is the global exponent minimum.

## Proved

Given:

- selected-width provenance;
- chart-level A0 extraction hypothesis;
- an active coordinate whose ratio is the displayed Theorem 2 lambda formula;
- a lower bound of that displayed ratio against every active coordinate;
- a chart whose `countInChartAtRatio displayedLambda` is the displayed order
  formula;
- a uniform upper bound on every chart's `countInChartAtRatio displayedLambda`;

Lean constructs `AoyagiTheorem2SuppliedChartFinalBoundary` and derives the
same lambda/order pair conclusion as the chart finite-certificate bridge.

The proof first derives
`Cnc.exponentData.exponentMinimum = displayedLambda` and only then uses the A0
ratio-count theorem to convert ratio-count data into the exponent order.

## Not Proved

No chart certificate, chart coverage, analytic unit nonvanishing,
active-ratio lower bound, ratio-count witness, ratio-count upper bound, Lemma
5 exactness, pole order without A0, or RLCT extraction is proved.

## Verification

Focused target:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean
```

Full closeout should also run:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

Independent xhigh review passed:
`review-theorem2-chart-ratio-count-bridge-a6.md`.
