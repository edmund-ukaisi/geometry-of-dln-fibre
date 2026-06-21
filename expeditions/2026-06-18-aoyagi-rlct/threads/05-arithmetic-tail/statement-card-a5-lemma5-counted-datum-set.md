# Statement Card - A5 Lemma 5 Counted Datum Set

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5CountDatum`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5CountDatumNonbaseSet`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5CountDatumSet`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5CountDatumNonbaseSet_card`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5CountDatumSet_card`

## Claim

Given a supplied interior base value in each same-coordinate interval, the
finite set consisting of one base datum and all tagged nonbase interval values
has cardinality `a*(ell-a)+1`.

## Inputs

- `1 <= ell`.
- `a <= ell`.
- `baseValue j in aoyagiHtildeIntervalValueSetNat ell a M m j` for every
  `j in Icc 1 (ell-1)`.

## Proves

```text
(aoyagiLemma5CountDatumSet ell a M m baseValue).card
  = a*(ell-a)+1.
```

## Does Not Prove

- A source-backed map from lambda-vectors to counted data.
- Case 1(2) uniqueness or back-to-label coverage.
- Any supplied branch-family construction.
- Terminal-label exactness, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF p. 26, motivates the counted-data shape.  The Lean theorem
proves only the finite cardinality of this codomain using the already proved
interval arithmetic.
