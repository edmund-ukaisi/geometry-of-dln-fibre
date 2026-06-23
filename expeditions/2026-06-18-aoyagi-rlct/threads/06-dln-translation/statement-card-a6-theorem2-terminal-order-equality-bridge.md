# Statement card - A6 Theorem 2 terminal order equality bridge

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card_eq`

The module also provides pair-form `lambda_and_poleOrder...` consequences for
the same final-boundary variants.

## Claim

An exact terminal-minimum count

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula
```

can be used directly as the Theorem 2 finite exponent order field, after the
usual supplied exponent-minimum and chart-count certificates identify
`D.exponentOrder` with `TC.terminalMinimumLabels.card`.

## Proved

Lean proves finite exponent formula, supplied final-boundary, chart-final, and
pair-form wrappers.  The order proof is only transitivity:

```text
D.exponentOrder
  = TC.terminalMinimumLabels.card
  = data.theorem2OrderFormula.
```

The active-ratio variants reuse the existing finite minimum certificate.  The
chart-count variants reuse the existing finite `exponentOrder` max certificate
or displayed-ratio count rewrite.

## Assumed

The exact terminal count itself is supplied to this A6 bridge.  Depending on
the wrapper, the exponent-minimum formula, active-ratio lower bound,
chart/order equality, chart-count equality, selected-width provenance, and
normal-crossing extraction hypothesis remain explicit supplied inputs.

## Deferred

Eq5 endpoint-family construction, A5 classifier/injectivity/back-to-label
source proofs, source-backed no-extra terminal coverage, chart production,
chart coverage, active-ratio lower bounds, displayed-ratio chart-count facts,
pole order without A0, and RLCT extraction.

## Cited

Only the existing explicit normal-crossing extraction hypothesis in the final
boundary wrappers.  The finite equality bridge itself cites nothing.

## Verification

Focused Lean check and full library checks pass:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderEqualityBridge
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core/style warnings.

## Review

xhigh review passed.  Review artifact:
`review-theorem2-terminal-order-equality-bridge-a6.md`.
