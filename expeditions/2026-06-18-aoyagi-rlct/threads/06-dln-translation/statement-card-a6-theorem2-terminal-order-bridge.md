# Statement card - A6 Theorem 2 terminal-order bridge

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card`

## Claim

The finite exponent formula boundary for Aoyagi Theorem 2 can be built from:

- the supplied exponent-minimum formula;
- a supplied equality from normal-crossing chart order to Lemma 5 terminal
  minimum labels;
- supplied branch-label injectivity;
- the supplied terminal-minimum upper bound in `data.theorem2OrderFormula`
  notation.

With selected-width provenance and the A0 extraction hypothesis also supplied,
Lean derives the final ceiling-data pair:

```text
lambda = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data
poleOrder = data.theorem2OrderFormula
```

## Proved

Finite transitivity:

```text
D.exponentOrder
  = terminalMinimumLabels.card
  = data.theorem2OrderFormula.
```

The second equality is the existing Lemma 5 terminal-order bridge.

## Assumed

- `D.exponentMinimum = aoyagiTheorem2Lambda_fromCeilData ...`.
- `D.exponentOrder = TC.terminalMinimumLabels.card`.
- Branch-label injectivity on the supplied terminal family.
- `TC.terminalMinimumLabels.card <= data.theorem2OrderFormula`.
- Selected-width provenance for the final-boundary constructor.
- `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`.

## Deferred

Exponent-minimum computation, chart-order/terminal-label identification,
normal-crossing chart production, source-backed Lemma 5 no-extra coverage,
source-backed branch-label injectivity, source-backed terminal upper bound,
pole order without A0, and RLCT extraction.

## Cited

Only the A0 normal-crossing extraction interface is cited when using the final
pair theorem.  The finite bridge itself is bookkeeping over supplied
hypotheses.

## Verification

Focused Lean, module, aggregator, full-library, sorry, and diff checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderBridge
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

Independent xhigh review passed:
`review-theorem2-terminal-order-bridge-a6.md`.
