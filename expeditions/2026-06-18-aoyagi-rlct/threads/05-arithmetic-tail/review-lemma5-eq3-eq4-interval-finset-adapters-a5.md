# Review - Lemma 5 Eq3/Eq4 Interval Finset Adapters

Reviewers: controller review; xhigh exact-diff reviewer.
Verdict: endpoint/API wrappers are source-safe.

## Findings

No issue was found in the controller check.

No issue was found by the xhigh exact-diff reviewer.

The Eq4 wrapper combines:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt
aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
```

The Eq3 wrapper combines:

```text
aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
```

Both wrappers are conjunction adapters only.

## Checks

Controller check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
```

passed before this note was updated.

Exact-diff reviewer check:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
```

passed.  The controller also ran `lake build DLNFibre`; it passed with only
known pre-existing Core warnings.

## Residual Risks

These wrappers do not provide `LabelExponentCertificate` data, least values,
terminal exponents, displayed-vector construction, admissibility, chart
coverage, Lemma 5 order count, normal crossings, or RLCT extraction.
