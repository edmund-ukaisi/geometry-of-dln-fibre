# Reproduction - Lemma 5 Terminal Order Classifier Notation

Date: 2026-06-23.

Status: finite A5 handoff under supplied classifier/back-to-label hypotheses.

## Source Boundary

Aoyagi PDF pp. 25-27 gives the displayed terminal count shape used in the
Theorem 2 pole-order formula, but the expedition source audit records that
the printed Eq. (3)/(4)/(5) families do not by themselves supply the
Lean-level terminal classifier, branch-label injection, back-to-label map, or
full Lemma 4 witness.  This slice therefore proves no source-backed Lemma 5
exactness theorem.

The goal is narrower: expose already-proved supplied-boundary routes in
Aoyagi Theorem 2's order notation.

## Finite Calculation

Let

```text
data : AoyagiDefinition3CeilData (n+1) m
TC   : AoyagiLemma5SuppliedTerminalCandidateFamily
         ... n data.aParam data.ceilWidth m ...
```

The existing A5 terminal bridge proves two supplied upper-bound routes:

```text
UpperBoundClassifier
  -> terminalMinimumLabels.card
       <= data.aParam * (n + 1 - data.aParam) + 1

TerminalMinimumCountDatumBackToBranchLabel
  -> terminalMinimumLabels.card
       <= data.aParam * (n + 1 - data.aParam) + 1
```

and, with supplied branch-label injectivity and the selected-sum equality
already carried by `data`, exact-count routes:

```text
UpperBoundClassifier + branchLabel injective
  -> terminalMinimumLabels.card
       = data.aParam * (n + 1 - data.aParam) + 1

TerminalMinimumCountDatumBackToBranchLabel + branchLabel injective
  -> terminalMinimumLabels.card
       = data.aParam * (n + 1 - data.aParam) + 1
```

Definition 3's order formula is definitional:

```text
data.theorem2OrderFormula =
  data.aParam * ((n+1) - data.aParam) + 1.
```

Therefore each of the four existing supplied-boundary routes can be restated
with `data.theorem2OrderFormula` on the right-hand side.

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_upperBoundClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumBackToBranchLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumBackToBranchLabel_and_injOn
```

## Nonclaims

This does not construct an `UpperBoundClassifier`, counted-datum classifier,
back-to-label map, branch-label injectivity, Eq. (3)/(4)/(5) terminal
families, no-extra coverage, chart production, pole order, normal crossings,
or RLCT extraction.

## Kill Conditions

- Do not drop the supplied branch-label injectivity hypothesis from exact
  count wrappers.
- Do not present the classifier or back-to-label routes as source-backed.
- Do not treat the finite terminal count as pole order without the later A0/A6
  finite exponent and extraction boundaries.
