# Reproduction - Lemma 5 terminal branch introduced-domain capacity

Status: reproduced; Lean checked; xhigh review passed.

This note packages a finite-domain capacity consequence for a supplied terminal
candidate family.  It does not construct the terminal branches and does not
prove terminal-minimum exactness.

## Source

The supplied terminal-candidate family records, for every tagged supplied
branch, an introduced source label in the current finite domain

```text
introducedLabelFinset L width S J.
```

The already-proved supplied family count is

```text
C.fullBranches.card = a * (n + 1 - a) + 1.
```

## Reproduction

The supplied branch-label image is

```text
C.branchLabelImage = C.fullBranches.image C.branchLabel.
```

Every supplied branch label is introduced, so

```text
C.branchLabelImage <= introducedLabelFinset L width S J.
```

Finite-set monotonicity gives

```text
C.branchLabelImage.card <= (introducedLabelFinset L width S J).card.
```

If the supplied branch-label map is injective on `C.fullBranches`, then

```text
C.branchLabelImage.card = C.fullBranches.card.
```

Therefore

```text
C.fullBranches.card <= (introducedLabelFinset L width S J).card.
```

Finally, using the supplied full-branch count gives the numeric capacity bound

```text
a * (n + 1 - a) + 1 <= (introducedLabelFinset L width S J).card.
```

This last theorem is conditional: it says the introduced-label domain has room
for the supplied injected branch labels.  It is not a terminal-minimum count.

## Lean targets

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_introducedLabelFinset_card
AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_introducedLabelFinset_card_of_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_introducedLabelFinset_card_of_branchLabel_injOn
```

## Nonclaims

- No construction of terminal branch labels.
- No proof of branch-label injectivity.
- No no-extra terminal-minimum coverage.
- No terminal-minimum cardinality theorem.
- No pole order, normal crossings, or RLCT extraction.
