# Statement card - A5 Lemma 5 terminal minimum lower bound

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_terminalMinimumLabels_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_terminalMinimumLabels_card_of_branchLabel_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_terminalMinimumLabels_card_of_branchLabel_injOn`

## Claim

The supplied branch-label image gives a lower bound for the finite
terminal-minimum label set.  Under supplied branch-label injectivity, the
supplied branch count gives the numeric lower bound

```text
a * (n + 1 - a) + 1 <= C.terminalMinimumLabels.card.
```

## Proved

Only the easy lower-bound direction from supplied candidates attaining the
minimum.

## Assumed

The supplied terminal-candidate family, `a <= n+1`, the selected-width sum, and
for the full-branch/numeric statements the supplied branch-label injectivity.

## Deferred

No-extra terminal-minimum coverage, terminal-minimum upper bound, exact
terminal-minimum cardinality, pole order, normal crossings, and RLCT
extraction.

## Review

xhigh `Hume` passed the three-theorem slice with no findings.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge`
