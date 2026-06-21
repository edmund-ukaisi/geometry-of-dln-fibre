# Reproduction - Lemma 5 counted datum back-to-branch-label exactness

Date: 2026-06-21.

Scope: finite exactness packaging from supplied back-to-label data.  This
records that a supplied counted-datum back-to-label bridge, together with
supplied branch-label injectivity, gives the existing terminal-minimum
exactness boundary and exact cardinality.

This does not construct the classifier, back-to-label bridge, or branch-label
injectivity from Aoyagi's source.

## Source Inventory

The existing exactness boundary is

```text
C.TerminalMinimumLabelExactness
```

with fields:

```text
branchLabel_injOn :
  Set.InjOn C.branchLabel C.fullBranches

terminalMinimumLabels_subset_branchLabelImage :
  C.terminalMinimumLabels subset C.branchLabelImage
```

The supplied counted-datum back-to-label bridge already gives the second field
after forgetting the counted-datum equality:

```text
C.upperBoundClassifier_of_countDatumBackToBranchLabel
```

and the existing theorem

```text
C.terminalMinimumLabelExactness_of_upperBoundClassifier
```

packages that upper-bound classifier with supplied branch-label injectivity.

## Pen-And-Paper Derivation

Assume:

```text
hinj : branchLabel is injective on C.fullBranches,
classifier : C.TerminalMinimumCountDatumClassifier,
backToLabel : C.TerminalMinimumCountDatumBackToBranchLabel branchCoord classifier.
```

The back-to-label bridge supplies, for every terminal-minimum label, a branch
with the same branch label.  Hence every terminal-minimum label lies in
`C.branchLabelImage`, giving the no-extra field.  Together with `hinj`, this is
exactly `C.TerminalMinimumLabelExactness`.

For exact cardinality, additionally assume:

```text
ha : a <= n+1,
sum_i m_i = (n+1)*(M-1)+a.
```

The selected-width sum and `ha` give the already-proved easy inclusion from
the supplied branch-label image into terminal-minimum labels.  Exactness gives
the reverse inclusion and branch-label injectivity.  Therefore

```text
C.terminalMinimumLabels.card = C.branchLabelImage.card
                             = C.fullBranches.card
                             = a * (n+1-a) + 1.
```

## Lean Targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumBackToBranchLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumBackToBranchLabel
```

## Kill Conditions

- Do not claim branch-label injectivity is proved from Aoyagi's equations.
- Do not claim the counted-datum classifier or back-to-label bridge is
  constructed.
- Do not treat the exact-cardinality theorem as a pole-order theorem.
- Do not prove or claim normal crossings or RLCT extraction.
