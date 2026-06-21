# Statement Card - A5 Lemma 5 Upper-Bound Classifier Interface

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.UpperBoundClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_subset_branchLabelImage_of_upperBoundClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_terminalMinimumLabels_subset_branchLabelImage`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_iff_terminalMinimumLabels_subset_branchLabelImage`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_upperBoundClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_upperBoundClassifier`

## Claim

For a supplied terminal-candidate family, an `UpperBoundClassifier` is a
supplied map-on-membership from every terminal-minimum label to a supplied
branch whose label is the original label.  It gives the no-extra containment
and the finite upper count; with supplied branch-label injectivity, it also
packages terminal-minimum exactness.

## Inputs

- A supplied terminal-candidate family `C`.
- `UpperBoundClassifier C`.
- For the numeric upper count: `a <= n+1`.
- For exactness packaging only: supplied injectivity of `C.branchLabel` on
  `C.fullBranches`.

## Proves

```text
C.terminalMinimumLabels subset C.branchLabelImage
```

is equivalent to `UpperBoundClassifier C`;

and

```text
C.terminalMinimumLabels.card <= a*(n+1-a)+1.
```

The upper count does not require branch-label injectivity.  With branch-label
injectivity, it also constructs
`TerminalMinimumLabelExactness C`.

## Does Not Prove

- A source-backed classifier from Aoyagi's PDF.
- The label-to-vector or minimum-to-lambda bridges.
- Case 1(2) uniqueness/nonduplication.
- Branch-label injectivity.
- Pole order, `theta`, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF p. 26, motivates the desired upper-bound classifier at the
source-vector level.  This slice only names the missing classifier as supplied
finite data and proves its finite-set consequences.
