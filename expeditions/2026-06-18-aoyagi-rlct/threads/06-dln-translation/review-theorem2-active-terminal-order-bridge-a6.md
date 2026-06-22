# Review - Theorem 2 active-ratio terminal-order bridge

Date: 2026-06-22.

Reviewer: xhigh reviewer `Mill the 2nd`.

## Verdict

Pass.

## Findings

No findings.

## Scope Check

The A6 active-ratio terminal-order slice keeps the required hypotheses
supplied:

```text
p in D.activePairs
D.ratioAt p = aoyagiTheorem2Lambda_fromCeilData ...
forall p' in D.activePairs,
  aoyagiTheorem2Lambda_fromCeilData ... <= D.ratioAt p'
D.exponentOrder = TC.terminalMinimumLabels.card
Set.InjOn TC.branchLabel TC.fullBranches
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula
hselected : m = aoyagiSelectedReducedWidths H r C
hNC : AoyagiNormalCrossingExtractionHypothesis D lambda poleOrder
```

The bridge does not claim source-backed normal-crossing chart production,
active-ratio inequalities, chart/order identification, Lemma 5 no-extra
coverage, pole order without A0, normal crossings, or RLCT extraction.

## Checks

Reviewer checks:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderBridge
cd lean && scripts/sorries
cd lean && lake env lean DLNFibre.lean
git diff --check
```

`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.

Controller closeout additionally ran the full-library build.
