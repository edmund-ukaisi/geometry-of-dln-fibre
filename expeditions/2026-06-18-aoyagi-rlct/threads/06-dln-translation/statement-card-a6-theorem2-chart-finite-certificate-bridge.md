# Statement card - A6 Theorem 2 chart finite-certificate bridge

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary.of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount`

## Claim

The chart-certificate final boundary can be built from explicit finite A0
min/order witnesses instead of an opaque finite exponent formula field.

## Proved

Given:

- selected-width provenance `m = aoyagiSelectedReducedWidths H r cuts`;
- chart-level A0 extraction hypothesis;
- an active coordinate whose ratio is Aoyagi Theorem 2's displayed
  `lambda` expression;
- a lower bound of that displayed ratio against every active coordinate;
- a chart whose global-minimum-coordinate count is the displayed order
  formula;
- a uniform upper bound on all such chart counts;

Lean constructs `AoyagiTheorem2SuppliedChartFinalBoundary` and derives the
pair conclusion

```text
lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data
poleOrder = data.theorem2OrderFormula.
```

## Not Proved

No chart certificate is constructed.  No chart coverage, analytic unit
nonvanishing, active-ratio bound, chart-count witness, chart-count upper bound,
Lemma 5 count, normal-crossing extraction, pole order without A0, or RLCT
extraction is proved.

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
`review-theorem2-chart-finite-certificate-bridge-a6.md`.
