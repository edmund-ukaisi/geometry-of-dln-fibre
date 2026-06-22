# Statement card - A6 Theorem 2 finite certificate bridge

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Theorem2FiniteExponentBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2FiniteExponentFormulaHypothesis.of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2FiniteExponentFormulaHypothesis.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount`

## Claim

The supplied finite exponent formula boundary can be constructed from:

- an active coordinate whose ratio is the displayed Theorem 2 `lambda` value;
- a lower bound showing that displayed value is at most every active ratio;
- a chart whose global-minimum coordinate count is the displayed order value;
- an upper bound showing every chart count is at most that displayed order.

With the explicit A0 extraction hypothesis also supplied, Lean derives:

```text
lambda = aoyagiTheorem2Lambda_fromCeilData L ell H r m data
poleOrder = data.theorem2OrderFormula
```

## Proved

Finite composition of the A0 min/order certificate lemmas with the existing
A6 finite exponent formula boundary.

## Assumed

The normal-crossing exponent data `D`; the active-coordinate witness and all
active-ratio lower bounds; the realizing chart and all-chart upper bounds; and
for the final pair theorem, `AoyagiNormalCrossingExtractionHypothesis`.

## Deferred

Normal-crossing chart production, unit nonvanishing, Jacobian/prior exponent
correctness, active-ratio inequalities from the blow-up recursion, chart-count
upper bounds from Lemma 5, Lemma 5 no-extra coverage, pole order without A0,
and RLCT extraction.

## Cited

Only the A0 normal-crossing extraction interface is cited when using the final
pair theorem.  The finite boundary constructor cites nothing.

## Verification

Focused Lean, module, aggregator, full-library, sorry, and diff checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2FiniteExponentBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2FiniteExponentBridge
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

Independent xhigh review passed:
`review-theorem2-finite-certificate-bridge-a6.md`.
