# Statement Card - A5 Lemma 5 Eq5 Strict-Offset Rising Count

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min`

## Claim

In the rising region `1 <= p`, `p <= a`, and `p <= ell-a`, the strict
equation `(5)` offset-value set has cardinality `p-1`.

## Inputs

- Natural numbers `ell`, `a`, and `p`.
- Source range `a <= ell`.
- Rising-region guards `1 <= p`, `p <= a`, and `p <= ell-a`.
- Arbitrary `M` and selected-width family `m`.

## Proves

```text
(aoyagiLemma5Eq5OffsetValueSet ell a p M m).card = p - 1.
```

## Does Not Prove

- Construction of equation `(5)` displayed vectors.
- Source-label legality or actual-width dominance.
- Endpoint realisation by equation `(3)` or `(4)`.
- All-coordinate coverage, all-branch packaging, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF pp. 26-27, and the displayed interval count
profile on PDF p. 26.
