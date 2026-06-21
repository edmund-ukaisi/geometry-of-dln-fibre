# Reproduction - Lemma 5 counted datum back-to-branch-label card bound

Date: 2026-06-21.

Scope: finite bookkeeping after the supplied counted-datum back-to-branch-label
boundary.  This records that the supplied bridge gives the existing numeric
upper count for terminal-minimum labels.

This does not construct the counted-datum classifier, branch-coordinate map,
or back-to-label bridge from Aoyagi's equations.

## Source Inventory

The previous supplied boundary has data

```text
classifier : C.TerminalMinimumCountDatumClassifier
backToLabel : C.TerminalMinimumCountDatumBackToBranchLabel branchCoord classifier
```

where `backToLabel` assigns to each

```text
label in C.terminalMinimumLabels
```

a supplied branch with the same `branchLabel` and with matching counted datum.

The existing theorem

```text
C.upperBoundClassifier_of_countDatumBackToBranchLabel
```

forgets the counted-datum equality and keeps the branch-label witness, giving
the supplied no-extra classifier

```text
C.UpperBoundClassifier.
```

The existing theorem

```text
C.terminalMinimumLabels_card_le_of_upperBoundClassifier
```

then gives

```text
C.terminalMinimumLabels.card <= a * (n+1-a) + 1.
```

## Pen-And-Paper Derivation

Assume

```text
ha : a <= n+1.
```

By the supplied back-to-label bridge, every terminal-minimum label has a
supplied branch carrying that same label.  Hence the finite terminal-minimum
label set is included in the supplied branch-label image:

```text
C.terminalMinimumLabels subset C.branchLabelImage.
```

Therefore

```text
C.terminalMinimumLabels.card <= C.branchLabelImage.card.
```

The branch-label image is the image of `C.fullBranches`, so

```text
C.branchLabelImage.card <= C.fullBranches.card.
```

The supplied family count gives

```text
C.fullBranches.card = a * (n+1-a) + 1.
```

Combining the inequalities gives the desired numeric upper bound.

## Lean Target

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel
```

## Kill Conditions

- Do not claim the counted-datum classifier is constructed from Aoyagi's PDF.
- Do not claim the branch-coordinate map or back-to-label bridge is constructed.
- Do not claim branch-label injectivity or exact cardinality.
- Do not claim pole order, normal crossings, or RLCT extraction.
