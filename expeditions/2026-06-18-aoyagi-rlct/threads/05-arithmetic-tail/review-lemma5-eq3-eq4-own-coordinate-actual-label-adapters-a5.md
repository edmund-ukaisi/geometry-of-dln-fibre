# Review - Lemma 5 equations (3)/(4) own-coordinate actual-label adapters

Reviewer: `Poincare the 2nd` (xhigh Lean/API scout) and controller check.
Verdict: valid adapter layer.

## Findings

No issue was found with the adapter statements.

For equation `(4)`, the proof combines:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility
```

The only new step is rewriting by `k=Htilde_p+1`.

For equation `(3)`, the proof combines:

```text
aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack
```

The explicit slack remains in the statement, as required by the existing
counterexample.

The last-cutpoint wrappers are valid thin source-range refinements.  For Eq4,
the supplied equation `(4)` guards imply `p<ell`, so the own left endpoint is
in block `p`; for Eq3, `1<=a<ell` implies the own left endpoint is in block
`1`.  The existing selected-block source-range helper then derives the upper
range from `C.point ell<=L+1`.

## Source Fidelity

These theorems do not assert the existence of the displayed vectors.  They
start from supplied piecewise certificates and source-layer compatibility
hypotheses.  This matches the current conservative boundary for Lemma 5:
source-vector construction, terminality, and chart sequence remain open.

## Checks

Controller check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
```

passed for the landed theorem draft before this review note was written.

## Residual Risks

The wrappers are useful API cleanup.  They do not advance the blocked
displayed-family realisation theorem by themselves.
