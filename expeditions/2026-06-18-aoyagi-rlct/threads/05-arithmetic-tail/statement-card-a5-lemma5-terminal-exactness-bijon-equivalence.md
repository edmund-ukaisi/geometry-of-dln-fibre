# Statement card - A5 Lemma 5 terminal exactness/bijection equivalence

## Lean Name

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_bijOn`

## Claim

For a supplied terminal-candidate family, packaged terminal-minimum exactness
is equivalent to the branch-label bijection

```text
Set.BijOn C.branchLabel C.fullBranches C.terminalMinimumLabels.
```

The forward direction assumes `a <= n+1` and the selected-width sum through the
existing branch-label-to-terminal-minimum theorem.

## Proved

Lean combines the two existing directional wrappers:

- `branchLabel_bijOn_terminalMinimumLabels_of_exactness`;
- `terminalMinimumLabelExactness_of_branchLabel_bijOn`.

## Assumed

The terminal-candidate family, `a <= n+1`, and the selected-width sum are
supplied.  Either exactness or the bijection is supplied depending on the
direction.

## Deferred

Source construction of exactness, no-extra containment, classifier,
back-to-label map, branch-label injectivity, source labels, source branch
coverage, pole order, normal crossings, and RLCT extraction.

## Review

- Focused Lean check passed for `Lemma5TerminalBridge.lean`.
- Independent xhigh reviewer `Epicurus` found no blocking issue and confirmed
  the theorem remains finite supplied-label API.
