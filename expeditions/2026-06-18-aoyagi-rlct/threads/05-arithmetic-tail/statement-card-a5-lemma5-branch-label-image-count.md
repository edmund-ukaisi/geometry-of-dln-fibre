# Statement Card - A5 Lemma 5 Branch-Label Image Count

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_mem_introducedLabelFinset`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_subset_introducedLabelFinset`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_eq_fullBranches_card_of_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_terminalCandidateData`

## Claim

For a supplied terminal-candidate family, the finite image of the supplied
branch-to-label map has the same cardinality as the tagged branch set whenever
that map is injective on the tagged branch set.  Hence, under supplied
injectivity, the distinct supplied-label image has cardinality
`a*(n+1-a)+1`.

Every label in this finite image inherits introduced-label status, terminal
least-value zero, and terminal exponent equal to the isolated Lemma 3 minimum
numerator.

## Inputs

- A supplied terminal-candidate family.
- The previous supplied branch count.
- Branch-label injectivity on `fullBranches`.
- For terminal-exponent data on image members: the selected-width sum
  hypothesis and `a <= n+1`.

## Proves

- Each supplied branch label belongs to `introducedLabelFinset`, and the
  branch-label image is a subset of that finite introduced-label set.
- `branchLabelImage.card = fullBranches.card` under supplied injectivity.
- `branchLabelImage.card = a*(n+1-a)+1` under supplied injectivity and the
  supplied Lemma 5 branch-count hypotheses.
- Each label in `branchLabelImage` satisfies the same introduced/least-value
  zero/terminal-exponent data as the branch that maps to it.

## Does Not Prove

- Source-backed injectivity of branch labels.
- Coverage of all terminal minimizers or absence of extra terminal minimizers.
- Pole order, normal crossings, `lambda`, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 24-27, motivates the target count.  This Lean slice is
only the elementary finite image-cardinality layer after the candidate branch
family and labels have been supplied.
