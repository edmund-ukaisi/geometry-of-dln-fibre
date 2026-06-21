# Statement Card - A5 Lemma 5 Eq3/Eq4 Interval Finset Adapters

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint`

## Claim

For supplied equation `(4)` and `(3)` piecewise certificates, the own-coordinate
branch value is simultaneously:

```text
in the same-coordinate Htilde interval,
equal to k - 1,
represented by Sigma.mk S k in introducedLabelFinset L n S k.
```

Eq4 packages the lower endpoint at coordinate `p`; Eq3 packages the upper
endpoint at coordinate `1`.

## Inputs

- Existing supplied Eq4 or Eq3 piecewise certificate.
- Existing source-selected hypotheses for the own-coordinate theorem.
- Last-cutpoint range and actual-width compatibility hypotheses for the
  source-label adapter.
- Eq3's explicit one-unit slack hypothesis.

## Proves

Only conjunction adapters over already-proved endpoint interval membership and
already-proved finite-domain introduced-label wrappers.

## Does Not Prove

- Construction of Eq3 or Eq4 displayed vectors.
- Endpoint realisation by an admissible chart family.
- Terminality, admissibility, chart coverage, Lemma 5 order count, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(3)` and `(4)`, PDF pp. 26-27.
