# Statement Card - A5 Lemma 5 Terminal Minimum Label Bijection API

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_exactness`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_branchLabel_bijOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_branchLabel_bijOn`

Commit pin: `78f16e1`.

## Claim

The supplied terminal-minimum exactness boundary can be expressed equivalently
as a `Set.BijOn` from supplied branches to terminal minimum labels.  A supplied
bijection gives the same finite count
`terminalMinimumLabels.card = a*(n+1-a)+1`.

## Proved

- Exactness implies `Set.BijOn branchLabel fullBranches terminalMinimumLabels`.
- Such a bijection implies `TerminalMinimumLabelExactness`.
- Such a bijection gives the finite terminal-minimum label count.

## Assumed

- The supplied terminal-candidate family.
- For the exactness-to-bijection theorem: `a <= n+1`, the selected-width sum,
  and `TerminalMinimumLabelExactness`.
- For the bijection-to-count theorem: `a <= n+1` and the supplied bijection.

## Cited

None.

## Deferred

- Source-backed construction of the bijection.
- Source-backed branch-label injectivity.
- Source-backed no-extra-minimizer containment.
- Pole order, normal crossings, and RLCT extraction.

## Status

Sorry-free focused build; review pending.
