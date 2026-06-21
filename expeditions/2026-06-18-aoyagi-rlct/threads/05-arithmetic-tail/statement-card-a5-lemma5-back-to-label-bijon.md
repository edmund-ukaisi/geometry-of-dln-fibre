# Statement card - A5 Lemma 5 counted-datum back-to-label bijection

## Lean Name

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumBackToBranchLabel`

## Claim

For a supplied terminal-candidate family, a supplied counted-datum classifier,
a supplied counted-datum back-to-label bridge, and supplied branch-label
injectivity give a bijection

```text
Set.BijOn C.branchLabel C.fullBranches C.terminalMinimumLabels.
```

## Proved

Lean composes existing supplied-boundary API:

- `terminalMinimumLabelExactness_of_countDatumBackToBranchLabel` packages
  supplied back-to-label and branch-label injectivity as terminal-minimum
  exactness;
- `branchLabel_bijOn_terminalMinimumLabels_of_exactness` turns that exactness
  into the finite bijection.

## Assumed

The terminal-candidate family fields, `a <= n+1`, the selected-width sum, a
counted-datum classifier, a counted-datum back-to-label bridge, and
branch-label injectivity are all supplied.

## Deferred

Source construction of the classifier, source construction of the
back-to-label bridge, branch-label injectivity from Aoyagi's printed families,
source labels, source branch coverage, terminal source realisation, pole
order, normal crossings, and RLCT extraction.

## Review

- xhigh source scout `Nietzsche` and pen-and-paper scout `Russell` confirmed
  that the source-backed no-extra bridge is not reproduced from the printed
  paragraph and that only supplied-boundary finite packaging is justified.
- xhigh Lean API scout `Hegel` proposed and typechecked this exact wrapper.
- Focused Lean check passed for `Lemma5TerminalBridge.lean`.
- Independent xhigh reviewer `Archimedes` found no blocking issue and
  confirmed the wrapper remains supplied-boundary finite API.
