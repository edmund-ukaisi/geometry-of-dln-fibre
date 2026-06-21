# Statement card - A5 Lemma 5 terminal branch introduced-domain capacity

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_introducedLabelFinset_card`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_introducedLabelFinset_card_of_branchLabel_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_introducedLabelFinset_card_of_branchLabel_injOn`

## Claim

For a supplied terminal-candidate family, the supplied branch-label image has
cardinality bounded by the current introduced-label finite domain.  If the
supplied branch-label map is injective on the supplied full branch set, then
the full branch set itself has cardinality bounded by that same domain.

With the supplied branch-family count, this gives

```text
a * (n + 1 - a) + 1 <= (introducedLabelFinset L width S J).card.
```

## Proved

Only finite-set capacity statements inside `introducedLabelFinset`.

## Assumed

The supplied terminal-candidate family, and for the branch/full-count
statements the supplied branch-label injectivity and `a <= n+1`.

## Deferred

Branch-label construction, proof of branch-label injectivity, no-extra
terminal-minimum coverage, exact terminal-minimum cardinality, pole order,
normal crossings, and RLCT extraction.

## Review

xhigh `Hume` passed the three-theorem slice with no findings and recommended
the final `suppliedBranchCount...` name.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge`
