# Statement Card - A6 Theorem 2 Eq5 Terminal-Order Bridge

## Lean File

`lean/DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean`

## Claim

A supplied Eq5 endpoint block-width payload can discharge the exact terminal
count input required by the existing A6 Theorem 2 exact-count sockets:

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

All global chart and analytic obligations remain explicit.

## Lean Names

```text
AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload
AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload.terminalMinimumLabels_card_eq_theorem2OrderFormula

AoyagiLemma5SuppliedTerminalCandidateFamily
  .theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiLemma5SuppliedTerminalCandidateFamily
  .theorem2SuppliedFinalBoundary_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiLemma5SuppliedTerminalCandidateFamily
  .theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiLemma5SuppliedTerminalCandidateFamily
  .lambda_and_poleOrder_eq_of_chart_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

## Proved

Lean proves a finite composition:

```text
Eq5 endpoint block-width payload
  -> exact terminal count
  -> existing A6 finite/final/chart-final exact-count wrappers.
```

## Assumed

The Eq5 payload is supplied.  The active coordinate, active-ratio lower bound,
displayed-ratio chart count, all-chart upper bound, selected-width provenance,
and normal-crossing extraction hypothesis remain supplied.  In the
final-boundary wrappers, selected-width provenance is stated for the same
selected cutpoints `P.cut` carried by the supplied Eq5 payload.

## Not Proved

No Eq5 source family construction, no source-backed Lemma 5 exactness, no
global chart production, no chart coverage, no active-ratio bound, no
displayed-ratio chart-count theorem, no pole order without A0, and no RLCT
extraction.

## Cited

Only the existing explicit normal-crossing extraction hypothesis in the final
boundary wrappers.  The finite Eq5-to-A6 handoff itself cites nothing.

## Verification

Run:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Theorem2Eq5TerminalOrderBridge
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```
