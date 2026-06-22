# Statement card - A6/A0 Theorem 2 finite exponent bridge

## Claim

If finite normal-crossing exponent data has the same finite minimum and finite
order count as Aoyagi Theorem 2's displayed arithmetic, and if the A0
normal-crossing extraction hypothesis identifies external `lambda` and
`poleOrder` with those finite exponent values, then `lambda` and `poleOrder`
equal the displayed Aoyagi formulas.

## Lean names

File: `lean/DLNFibre/DLN/Aoyagi/Theorem2FiniteExponentBridge.lean`.

- `AoyagiTheorem2FiniteExponentFormulaHypothesis`
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.lambda_eq_theorem2Lambda_fromCeilData_of_extractionHypothesis`
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.lambda_eq_theorem2Lambda_average_of_extractionHypothesis`
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.lambda_eq_theorem2Lambda_expanded_of_extractionHypothesis`
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.poleOrder_eq_theorem2OrderFormula_of_extractionHypothesis`
- `AoyagiTheorem2FiniteExponentFormulaHypothesis.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_extractionHypothesis`

Finite min/order certificate constructors are recorded separately in
`statement-card-a6-theorem2-finite-certificate-bridge.md`.

## Hypotheses

- `AoyagiTheorem2FiniteExponentFormulaHypothesis D L ell H r m data`, supplying:
  `D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData ...` and
  `D.exponentOrder = data.theorem2OrderFormula`.
- `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`, the explicit
  A0 cited-boundary hypothesis, where `poleOrder` is only the order parameter
  supplied by that explicit equality package.
- The existing `AoyagiDefinition3CeilData ell m`, including `0 < ell` and
  `0 < a <= ell`.

## Status

Proved in Lean as conditional bridge only.

## Explicit exclusions

This does not construct the exponent data, prove the finite exponent
equalities, prove source parameter provenance `m = H(S_j)-r`, prove Definition
3 selected-cutpoint inequalities or existence, prove rank-width hypotheses,
prove chart coverage, prove unit factors, prove Jacobian/prior exponent
correctness, prove normal crossings, prove Lemma 5 exactness/order count, prove
the analytic extraction theorem, or assert a final unconditional RLCT theorem.
