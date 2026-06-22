# Statement card - A6 Theorem 2 active chart-terminal-order bridge

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_chartCount_terminalMinimumLabels_card`

## Claim

The A6 finite exponent formula boundary can be built from:

- a supplied active coordinate whose A0 ratio is the displayed Theorem 2
  `lambda` value;
- a supplied lower bound showing that value is at most every active ratio;
- a supplied chart whose global-minimum coordinate count is
  `TC.terminalMinimumLabels.card`;
- a supplied upper bound showing every chart count is at most
  `TC.terminalMinimumLabels.card`;
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

Finite composition:

```text
active ratio witness + all-active lower bound
  => D.exponentMinimum = displayed Theorem 2 lambda

chart count witness + all-chart upper bound
  => D.exponentOrder = terminalMinimumLabels.card

terminalMinimumLabels.card = data.theorem2OrderFormula
  => D.exponentOrder = data.theorem2OrderFormula
```

The terminal-label equality is the existing A5 terminal-order bridge.

## Assumed

- The normal-crossing exponent data `D`.
- The active-coordinate witness and active-ratio lower bound.
- The chart-count witness and all-chart upper bound.
- Branch-label injectivity on the supplied terminal family.
- `TC.terminalMinimumLabels.card <= data.theorem2OrderFormula`.
- Selected-width provenance for the final-boundary constructor.
- `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`.

## Deferred

Normal-crossing chart production, unit nonvanishing, Jacobian/prior exponent
correctness, active-ratio inequalities from the blow-up recursion, chart-count
upper bounds from source charts, source-backed chart-count/terminal-label
identification, source-backed Lemma 5 no-extra coverage, source-backed
branch-label injectivity, source-backed terminal upper bound, pole order
without A0, and RLCT extraction.

## Cited

Only the A0 normal-crossing extraction interface is cited when using the final
pair theorem.  The finite boundary constructors cite nothing.

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
`review-theorem2-active-chart-terminal-order-bridge-a6.md`.
