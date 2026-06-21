# Reproduction - Lemma 5 terminal minimum lower bound

Status: reproduced; Lean checked; xhigh review passed.

This note packages the easy lower-bound direction for the supplied terminal
candidate family.  It does not prove no-extra coverage or exact terminal
minimum cardinality.

## Source

The supplied terminal-candidate family already proves that every supplied
branch label is an introduced label with terminal least value zero and the
minimum numerator.  In Lean this is recorded by

```text
C.branchLabelImage <= C.terminalMinimumLabels.
```

This is the easy direction: supplied candidates attain the minimum.

## Reproduction

Finite-set monotonicity gives

```text
C.branchLabelImage.card <= C.terminalMinimumLabels.card.
```

If the supplied branch-label map is injective on the supplied full branch set,
then

```text
C.branchLabelImage.card = C.fullBranches.card.
```

Therefore

```text
C.fullBranches.card <= C.terminalMinimumLabels.card.
```

Using the supplied branch-family count,

```text
C.fullBranches.card = a * (n + 1 - a) + 1,
```

we get the numeric lower bound

```text
a * (n + 1 - a) + 1 <= C.terminalMinimumLabels.card.
```

This is not the no-extra upper bound.  Terminal-minimum labels may still exist
outside the supplied branch-label image.

## Lean targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_terminalMinimumLabels_card_of_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_terminalMinimumLabels_card_of_branchLabel_injOn
```

## Nonclaims

- No no-extra terminal-minimum coverage.
- No terminal-minimum upper bound or exact count.
- No construction of branch-label injectivity.
- No pole order, normal crossings, or RLCT extraction.
