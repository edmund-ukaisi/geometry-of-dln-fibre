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
