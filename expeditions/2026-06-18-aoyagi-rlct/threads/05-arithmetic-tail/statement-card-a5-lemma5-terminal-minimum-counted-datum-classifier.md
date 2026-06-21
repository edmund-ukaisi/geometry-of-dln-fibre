# Statement Card - A5 Lemma 5 Terminal-Minimum Counted-Datum Classifier

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumClassifier`

## Claim

If the finite terminal-minimum label set has a supplied injective classifier
into the counted same-coordinate interval datum set, then it has Aoyagi's
Lemma 5 upper cardinality bound.

## Inputs

- A supplied terminal-candidate family `C`.
- `a <= n+1`.
- A supplied counted-datum classifier on `C.terminalMinimumLabels`.

## Proves

```text
C.terminalMinimumLabels.card <= a*(n+1-a)+1.
```

## Does Not Prove

- The classifier from Aoyagi's source.
- Branch-label image equality or exactness.
- Source-label legality, source-vector construction, injection, or
  back-to-label coverage.
- Pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF p. 26, motivates an upper bound by counting interval
values.  This slice only states the finite classifier needed to make that
upper-bound argument precise.
