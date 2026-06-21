# Statement Card - A5 Lemma 5 Counted Datum Classifier

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5CountDatumClassifier`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5CountDatumClassifier.image_subset_countDatumSet`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5CountDatumClassifier.candidates_card_le`

## Claim

If a finite candidate set injects into the counted datum set, then its
cardinality is at most `a*(ell-a)+1`.

## Inputs

- A finite `candidates : Finset alpha`.
- A counted datum classifier into
  `aoyagiLemma5CountDatumSet ell a M m baseValue`.
- `1 <= ell`.
- `a <= ell`.
- The supplied base-value membership used to count the codomain.

## Proves

```text
candidates.card <= a*(ell-a)+1.
```

## Does Not Prove

- A source-backed candidate set.
- A source-backed classifier from lambda-vectors.
- Case 1(2) uniqueness or back-to-label coverage.
- Terminal-label exactness, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF p. 26, motivates the desired upper-bound injection into
interval data.  This slice only packages that injection as supplied finite
data and proves the resulting cardinal inequality.
