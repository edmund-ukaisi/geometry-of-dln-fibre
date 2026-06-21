# Statement Card - A5 Lemma 5 Eq5 Post-p Lower Obstruction

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_postP_belowLower_of_intervalExcess_lt_offset`

## Claim

For a supplied equation `(5)` piecewise certificate, a post-`p` branch value is
strictly below the lower Htilde chain whenever the post-branch subtraction
`alpha+b-p` exceeds the Htilde interval excess at coordinate `b`.

## Inputs

- A supplied `AoyagiLemma5Eq5PiecewiseSourceVector`.
- A selected block point `C.block b S`.
- Post-`p` range hypotheses `p <= b` and `b <= p + (a-alpha)`.
- Gap hypothesis

```text
aoyagiLemma5IntervalExcess ell a b < alpha + b - p
```

## Proves

```text
T S < aoyagiHtildeLowerNat ell a M m b
```

## Does Not Prove

- Construction of the displayed Eq5 source vector.
- Failure of all Eq5 branches.
- A corrected Eq5 construction.
- Source-label legality, terminality, chart coverage, classifier coverage,
  branch-label injectivity, back-to-label coverage, pole order, normal
  crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, displays equation `(5)` as part of the branch
family.  This slice is the elementary arithmetic check of the post-`p` clause
against the lower Htilde bound.
