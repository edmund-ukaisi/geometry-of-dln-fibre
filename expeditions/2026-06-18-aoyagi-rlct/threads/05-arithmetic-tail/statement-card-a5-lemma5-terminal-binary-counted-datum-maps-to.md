# Statement Card - A5 Lemma 5 Terminal Binary Counted-Datum Maps-To

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5CountDatumSet_mem_of_terminalH_binaryIncrementPrefixDelta`

## Claim

A single terminal binary-prefix-delta `H`-chain at an interior coordinate gives
a nonbase counted datum, provided its value is not the supplied base value.

## Inputs

- `j in Finset.Icc 1 (ell-1)`.
- `a <= ell`.
- `H 0 = m 0`.
- `H (Fin.last ell) = 0`.
- `sum_i m_i = ell*(M-1)+a`.
- Binary prefix-delta hypotheses for `H`.
- `H_j != baseValue j`.

## Proves

```text
some (j, H_j) in aoyagiLemma5CountDatumSet ell a M m baseValue.
```

Here `H_j` is the interior-coordinate component
`H (aoyagiLemma5InteriorCoord ell j hj)`.

## Does Not Prove

- Source-vector construction or vector-to-chain correspondence.
- Coordinate-wise coverage.
- Classifier injection or back-to-label coverage.
- Terminal-label exactness, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 25-27, motivates classifying terminal candidates by
same-coordinate interval data.  This Lean slice proves only the conditional
finite maps-to step from already-supplied terminal binary chain data.
