# Statement Card - A5 Lemma 5 Counted-Datum Classifier Order-Formula Bridge

## Lean Names

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumClassifier_and_branchLabel_injOn
```

## Claim

For Definition 3 ceil data with `ell = n+1`, a supplied terminal-minimum
counted-datum classifier gives the terminal-minimum upper bound in Aoyagi
Theorem 2 order notation:

```text
TC.terminalMinimumLabels.card <= data.theorem2OrderFormula.
```

Adding supplied branch-label injectivity gives

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

## Inputs Kept Explicit

- `data : AoyagiDefinition3CeilData (n+1) m`;
- a supplied terminal candidate family `TC`;
- a supplied `TC.TerminalMinimumCountDatumClassifier`;
- supplied branch-label injectivity for the equality theorem.

## Proved

Only finite handoff bookkeeping from the counted-datum upper-bound API to the
final order formula notation.

## Not Proved

No counted-datum classifier construction, branch-label injectivity proof,
back-to-label map, Eq3/Eq4/Eq5 branch coverage, source-label legality,
terminal `tilde t=0`, pole order, normal crossings, or RLCT extraction.
