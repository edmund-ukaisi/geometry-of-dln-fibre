# Review - Lemma 5 terminal minimum lower bound

Reviewer: xhigh `Hume`.

Scope:

- `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_terminalMinimumLabels_card`;
- `AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_terminalMinimumLabels_card_of_branchLabel_injOn`;
- `AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_terminalMinimumLabels_card_of_branchLabel_injOn`.

## Findings

None.

## Verdict

Pass.  The theorems are formally correct and scoped honestly.  The first is
`Finset.card_le_card` applied to
`C.branchLabelImage_subset_terminalMinimumLabels ha hselected`.  The second
correctly needs supplied branch-label injectivity to identify branch count with
image count.  The third uses the supplied full-branch count.

The nonclaims are appropriate: this proves only the easy lower-bound direction
and does not prove no-extra coverage, upper bound, exact terminal-minimum
count, pole order, normal crossings, or RLCT extraction.

## Commands Run

- exact-name `rg` search for duplicates
- local inspection of the theorem block
- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`

## Residual Risk

The result remains conditional on supplied branch-label injectivity and the
existing supplied terminal-candidate family.  It does not source-produce the
missing no-extra/classifier data.
