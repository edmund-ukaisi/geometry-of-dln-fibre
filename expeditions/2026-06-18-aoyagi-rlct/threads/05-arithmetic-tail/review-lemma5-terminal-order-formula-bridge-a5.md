# Review - Lemma 5 terminal order formula bridge

Date: 2026-06-22.

Reviewer: xhigh post-implementation reviewer `Bernoulli the 2nd`.

## Verdict

Pass after aggregator import-order fix.

## Scope Check

No overclaiming was found in:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_theorem2OrderFormula_bound
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn
```

The bridge remains conditional on supplied branch-label injectivity and the
supplied upper bound.  It does not source-prove Lemma 5 no-extra coverage,
pole order, normal crossings, or RLCT.

## Finding Fixed

The first implementation inserted the new aggregator import before
`FinalFormula`, despite the aggregator rule to append new imports at the end.
The import has been moved to the end of `lean/DLNFibre.lean`.

## Checks

Focused Lean and module build for `Lemma5TerminalOrderBridge` passed.
Full-library verification is recorded in the statement card and closeout.
