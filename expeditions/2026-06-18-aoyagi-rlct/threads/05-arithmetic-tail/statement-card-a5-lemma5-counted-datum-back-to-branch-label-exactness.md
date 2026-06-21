# Statement Card - A5 Lemma 5 Counted Datum Back-To-Branch Label Exactness

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumBackToBranchLabel`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumBackToBranchLabel`

## Claim

A supplied counted-datum back-to-label bridge and supplied branch-label
injectivity give the packaged terminal-minimum exactness boundary.  With the
selected-width sum, this gives exact cardinality of terminal-minimum labels.

## Inputs

- A supplied terminal-candidate family `C`.
- Supplied branch-label injectivity on `C.fullBranches`.
- A branch-coordinate map.
- A supplied counted-datum classifier on `C.terminalMinimumLabels`.
- A supplied counted-datum back-to-label bridge.
- For exact cardinality: `a<=n+1` and the selected-width sum.

## Proves

```text
C.TerminalMinimumLabelExactness
```

and, with the selected-width sum,

```text
C.terminalMinimumLabels.card = a * (n + 1 - a) + 1.
```

## Does Not Prove

- The counted-datum classifier from Aoyagi's source.
- The branch-coordinate map.
- The back-to-label bridge from equations `(3)`, `(4)`, or `(5)`.
- Branch-label injectivity from source.
- Pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, motivates the counted interval data and
displayed branch formulas.  This slice packages the still-supplied exactness
data as finite Lean consequences.
