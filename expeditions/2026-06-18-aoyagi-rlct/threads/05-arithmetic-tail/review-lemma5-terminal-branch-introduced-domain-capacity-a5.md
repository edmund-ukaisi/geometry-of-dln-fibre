# Review - Lemma 5 terminal branch introduced-domain capacity

Reviewer: xhigh `Hume`.

Scope:

- `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_introducedLabelFinset_card`;
- `AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_introducedLabelFinset_card_of_branchLabel_injOn`;
- `AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_introducedLabelFinset_card_of_branchLabel_injOn`.

## Findings

None.

## Verdict

Pass.  The three theorems are honest finite-set consequences and do not
overclaim.  The first is immediate from
`branchLabelImage_subset_introducedLabelFinset`.  The second adds supplied
branch-label injectivity to identify the image cardinality with the full-branch
cardinality.  The third uses the supplied full-branch count to state the
numeric capacity bound.

## Commands Run

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`
- exact-name search for duplicates
- local read-only inspection of the surrounding APIs

## Residual Risk

The theorem is conditional on supplied branch-label injectivity.  It does not
construct branch labels, prove no-extra terminal-minimum coverage, or prove any
pole-order/RLCT result.
