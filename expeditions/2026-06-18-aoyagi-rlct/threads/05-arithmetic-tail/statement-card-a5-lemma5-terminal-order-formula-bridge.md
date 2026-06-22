# Statement card - A5 Lemma 5 terminal order formula bridge

## Lean Names

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_theorem2OrderFormula_bound`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn`

## Claim

For a supplied Lemma 5 terminal-candidate family whose parameters come from
`AoyagiDefinition3CeilData (n+1) m`, the existing terminal-exactness
obstruction can be stated using Aoyagi Theorem 2's order formula:

```text
TerminalMinimumLabelExactness
  iff branch-label injectivity
      and terminalMinimumLabels.card <= data.theorem2OrderFormula.
```

Consequently, if those two right-hand hypotheses are supplied, Lean proves

```text
terminalMinimumLabels.card = data.theorem2OrderFormula.
```

## Proved

This is a finite rewrite of the existing A5 cardinal-bound equivalence using
the definition

```text
data.theorem2OrderFormula =
  data.aParam * ((n+1) - data.aParam) + 1.
```

## Assumed

The terminal-candidate family, Definition 3 ceil data, supplied branch-label
injectivity, and a supplied terminal-minimum cardinal upper bound in final
order notation.

## Deferred

Source proof of the upper bound, source construction of branch-label
injectivity, no-extra coverage, classifier/back-to-label data, source labels,
chart coverage, pole order, normal crossings, and RLCT extraction.

## Cited

None.  This is finite bookkeeping over supplied hypotheses.

## Verification

Focused Lean, module, aggregator, full-library, sorry, and diff checks passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalOrderBridge
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reports only pre-existing Core warnings.

Independent xhigh review passed after an aggregator import-order fix:
`review-lemma5-terminal-order-formula-bridge-a5.md`.
