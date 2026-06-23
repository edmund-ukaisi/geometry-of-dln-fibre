# Statement card - A5 Lemma 5 terminal order classifier notation

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_upperBoundClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_upperBoundClassifier_and_branchLabel_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumBackToBranchLabel`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumBackToBranchLabel_and_injOn`

## Claim

For a supplied Lemma 5 terminal-candidate family whose parameters come from
`AoyagiDefinition3CeilData (n+1) m`, the existing supplied
`UpperBoundClassifier` and counted-datum back-to-label routes imply the
terminal-minimum upper bound in Aoyagi Theorem 2 order notation.  With
supplied branch-label injectivity, the same routes imply

```text
terminalMinimumLabels.card = data.theorem2OrderFormula.
```

## Proved

This is a finite rewrite of existing A5 theorems using the definitional
identity

```text
data.theorem2OrderFormula =
  data.aParam * ((n+1) - data.aParam) + 1.
```

## Assumed

The terminal-candidate family, Definition 3 ceil data, supplied upper-bound
classifier or counted-datum back-to-label data, and supplied branch-label
injectivity for the exact-count variants.

## Deferred

Source construction of the classifiers, back-to-label map, branch-label
injectivity, Eq. (3)/(4)/(5) terminal families, no-extra coverage, chart
production, pole order, normal crossings, and RLCT extraction.

## Cited

None.  This is finite bookkeeping over supplied hypotheses.

## Verification

Focused Lean, module, aggregator, full-library, sorry, and diff checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalOrderBridge
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre
cd lean && lake env lean DLNFibre.lean
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

Independent xhigh review passed:
`review-lemma5-terminal-order-classifier-notation-a5.md`.
