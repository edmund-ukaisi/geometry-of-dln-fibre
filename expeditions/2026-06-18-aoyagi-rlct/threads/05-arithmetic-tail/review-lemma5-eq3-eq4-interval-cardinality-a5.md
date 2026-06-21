# Review - Lemma 5 Eq3/Eq4 Interval Cardinality

Reviewers: controller review; Nietzsche the 2nd exact-diff xhigh review.
Verdict: PASS.

## Findings

The theorems use only:

```text
aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat
aoyagiHtildeIntervalValueSetNat_card_of_lt
aoyagiLemma5IntervalSize_eq_succ_of_le_min
aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min
```

This is cardinality bookkeeping for one supplied same-coordinate interval.

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

Nietzsche the 2nd exact-diff xhigh review passed with no blocking findings.
The review confirmed that the Lean theorems are cardinality consequences of
the existing supplied finite-set equality plus interval/Eq5 cardinality lemmas,
and that the docs/ledgers do not claim printed Eq3 legality, source-label
legality, displayed-vector construction, all-coordinate/all-branch coverage,
order count, normal crossings, or RLCT.

## Residual Risks

This theorem does not prove source-label legality, displayed-vector
construction, all-coordinate/all-branch coverage, Lemma 5 order count, normal
crossings, or RLCT extraction.
