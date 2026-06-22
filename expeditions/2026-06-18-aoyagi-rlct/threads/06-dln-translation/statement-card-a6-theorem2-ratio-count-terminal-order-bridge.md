# Statement card - A6 Theorem 2 ratio-count terminal-order bridge

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_ratioCount_terminalMinimumLabels_card`

## Claim

The A6 finite exponent formula boundary can be built from chart counts stated
at the displayed Theorem 2 lambda value, once an active-ratio certificate
proves that displayed value is `D.exponentMinimum`.

## Proved

Finite composition:

```text
active ratio witness + all-active lower bound
  => D.exponentMinimum = displayed Theorem 2 lambda

chart count at displayed lambda + all-chart upper bound at displayed lambda
  => D.exponentOrder = terminalMinimumLabels.card

terminalMinimumLabels.card = data.theorem2OrderFormula
  => D.exponentOrder = data.theorem2OrderFormula
```

The final pair theorem then uses selected-width provenance and the A0
extraction hypothesis to derive the displayed lambda and order equations.

## Assumed

- The normal-crossing exponent data `D`.
- The active-coordinate witness and active-ratio lower bound.
- A chart-count witness at the displayed lambda and all-chart upper bound at
  the displayed lambda.
- Branch-label injectivity on the supplied terminal family.
- `TC.terminalMinimumLabels.card <= data.theorem2OrderFormula`.
- Selected-width provenance for the final-boundary constructor.
- `AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder`.

## Deferred

Normal-crossing chart production, unit nonvanishing, Jacobian/prior exponent
correctness, active-ratio inequalities from the blow-up recursion, source
proof of chart counts at the displayed lambda, source-backed Lemma 5
no-extra coverage, source-backed branch-label injectivity, source-backed
terminal upper bound, pole order without A0, and RLCT extraction.

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
`review-theorem2-ratio-count-terminal-order-bridge-a6.md`.
