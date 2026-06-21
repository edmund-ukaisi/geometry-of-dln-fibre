# Statement Card - A5 Lemma 5 Counted Datum Back-To-Branch Label Card Bound

## Lean Name

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel`

## Claim

For a supplied terminal-candidate family, a supplied counted-datum classifier
and supplied back-to-label bridge give the numeric upper bound

```text
C.terminalMinimumLabels.card <= a * (n + 1 - a) + 1.
```

## Inputs

- `ha : a <= n+1`.
- A branch-coordinate map `branchCoord : beta -> Nat`.
- A supplied counted-datum classifier on `C.terminalMinimumLabels`.
- A supplied back-to-label bridge matching each classified counted datum to a
  supplied branch carrying the same terminal label.

## Proves

The terminal-minimum label set has cardinality at most the supplied Lemma 5
count.

## Does Not Prove

- The counted-datum classifier from Aoyagi's source.
- The branch-coordinate map.
- The back-to-label bridge from equations `(3)`, `(4)`, or `(5)`.
- Branch-label injectivity or exact cardinality.
- Pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, motivates the counted interval data and
displayed branch formulas.  This slice is finite bookkeeping from supplied
classifier/back-to-label data.
