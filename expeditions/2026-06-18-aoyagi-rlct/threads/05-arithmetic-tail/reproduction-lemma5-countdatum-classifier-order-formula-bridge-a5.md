# Reproduction - Lemma 5 counted-datum classifier order-formula bridge

Date: 2026-06-22.

Status: finite A5-to-final-order handoff.  This is not a source-backed
classifier theorem.

## Source Boundary

Aoyagi Lemma 5, PDF pp. 25-27, gives the intended interval-count upper bound
and final order

```text
theta = a(ell-a)+1.
```

The expedition source audits record that the printed paragraph does not by
itself construct the Lean-level counted-datum classifier, its injectivity, or
the back-to-label map for every terminal-minimum label.  Those data remain
supplied.

## Finite Calculation

Let

```text
data : AoyagiDefinition3CeilData (n+1) m
TC   : AoyagiLemma5SuppliedTerminalCandidateFamily
         ... n data.aParam data.ceilWidth m ...
```

The existing counted-datum API proves that a supplied terminal-minimum counted
datum classifier gives

```text
TC.terminalMinimumLabels.card
  <= data.aParam * (n+1 - data.aParam) + 1.
```

By definition,

```text
data.theorem2OrderFormula =
  data.aParam * ((n+1) - data.aParam) + 1.
```

Therefore a supplied counted-datum classifier supplies exactly the
`data.theorem2OrderFormula` upper bound used by the terminal-order bridge.
Adding supplied branch-label injectivity gives the already-proved terminal
exactness cardinal squeeze:

```text
TC.terminalMinimumLabels.card = data.theorem2OrderFormula.
```

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumClassifier_and_branchLabel_injOn
```

## Nonclaims

This does not construct the counted-datum classifier, branch-label
injectivity, a back-to-label map, Eq3/Eq4/Eq5 branch coverage, source labels,
terminal `tilde t=0`, pole order, normal crossings, or RLCT extraction.
