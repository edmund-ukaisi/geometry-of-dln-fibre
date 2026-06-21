# Review - Lemma 5 Eq4 Lower Plus Eq5 Offset Count

Reviewers: controller review; Tesla the 2nd exact-diff xhigh review.
Verdict: PASS.

## Findings

The theorem uses only:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min
aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min
aoyagiLemma5IntervalExcess_eq_self_of_le_min
```

This is finite count bookkeeping for one supplied Eq4 lower endpoint plus the
strict Eq5 offset set.

## Checks

Controller checks:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
cd lean && scripts/sorries
git diff --check
cd lean && lake build DLNFibre
```

The full build produced only pre-existing Core warnings in `RankPattern`,
`DeformationExt`, `CThetaQIP`, `CThetaQIPConverse`, and `CThetaValue`.

Tesla the 2nd exact-diff xhigh review passed with no blocking findings.  The
review confirmed that the Lean theorem states only the cardinality effect of
inserting the supplied Eq4 own-coordinate value into the Eq5 strict offset set,
and that the notes/ledgers do not claim source-label legality,
displayed-vector construction, endpoint realisation, all-coordinate coverage,
order count, normal crossings, or RLCT.

## Residual Risks

This theorem does not prove source-label legality, displayed-vector
construction, upper endpoint realisation, all-coordinate/all-branch coverage,
Lemma 5 order count, normal crossings, or RLCT extraction.
