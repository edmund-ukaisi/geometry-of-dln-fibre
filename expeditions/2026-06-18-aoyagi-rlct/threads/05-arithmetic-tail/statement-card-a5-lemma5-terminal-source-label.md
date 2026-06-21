# Statement Card - A5 Lemma 5 Terminal Source Label

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_terminalSourceIndex_pos`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_terminal_actualWidthLabel_of_lastPoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_terminal_intervalValue_mem_introducedLabelFinset_of_terminalZero`

## Claim

At the terminal selected coordinate, the supplied terminal value `0` can be
paired with the legal source label `k=1`, under explicit source-range and
width-positivity hypotheses.

## Inputs

- `1 <= ell`.
- `a <= ell`.
- Selected-width sum
  `sum m = ell * (M - 1) + a`.
- Terminal range hypothesis `C.point ell <= L + 1`.
- Terminal width positivity `1 <= n(C.point ell)`.
- Supplied terminal source-coordinate equality
  `T(C.point ell - 1) = 0`.

## Proves

```text
actualWidthLabel L n (C.point ell - 1) 1
```

and

```text
T(C.point ell - 1) in aoyagiHtildeIntervalValueSetNat ell a M m ell
T(C.point ell - 1) = (1 : Int) - 1
Sigma.mk (C.point ell - 1) 1
  in introducedLabelFinset L n (C.point ell - 1) 1
```

## Does Not Prove

- Construction of the terminal source branch.
- Source-realisation equality from a supplied branch chain.
- Terminal-minimum-label exactness.
- Classifier coverage, branch-label injectivity, or back-to-label coverage.
- Pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 25-27, uses the terminal endpoint in the final
counting discussion.  This slice proves only the elementary source-label
bookkeeping for the terminal singleton, not the surrounding classifier or
chart-family construction.
