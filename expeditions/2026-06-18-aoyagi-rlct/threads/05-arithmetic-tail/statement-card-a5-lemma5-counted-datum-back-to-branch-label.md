# Statement Card - A5 Lemma 5 Counted Datum Back-To-Branch Label

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.branchCountDatumOfCoord`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumBackToBranchLabel`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_countDatumBackToBranchLabel`

## Claim

For a supplied terminal-candidate family, a supplied bridge from the
terminal-minimum counted-datum classifier back to supplied branch labels gives
the existing `UpperBoundClassifier`.

## Inputs

- A supplied terminal-candidate family `C`.
- A branch-coordinate map `branchCoord : beta -> Nat`.
- A supplied counted-datum classifier on `C.terminalMinimumLabels`.
- A supplied back-to-label bridge matching each terminal label's counted datum
  with a supplied branch carrying the same terminal label.

## Proves

```text
C.UpperBoundClassifier
```

and hence the existing no-extra containment into `C.branchLabelImage`.

## Does Not Prove

- The counted-datum classifier from Aoyagi's PDF.
- The branch-coordinate map.
- The back-to-label bridge from Aoyagi's displayed equations.
- Branch-label injectivity.
- Pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, motivates the counted interval data and
displayed branch formulas.  This slice only packages the missing
back-to-label step as supplied finite data.
