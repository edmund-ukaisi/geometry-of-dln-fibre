# Review - Lemma 5 Eq5 Strict-Offset Rising Count

Reviewers: controller review; Sartre the 2nd exact-diff xhigh review.
Verdict: PASS.

## Findings

The theorem uses only:

```text
aoyagiLemma5Eq5OffsetValueSet_card
aoyagiLemma5IntervalExcess_eq_self_of_le_min
Nat.min_eq_right
```

This is a finite count specialization.  It does not introduce source-label,
displayed-vector, chart, or order-count claims.

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

Sartre the 2nd exact-diff xhigh review passed with no blocking findings.  The
review confirmed that the Lean theorem proves only the one-coordinate
strict-offset count under rising-region guards and that the new docs/ledgers
do not claim displayed-vector construction, source-label legality, endpoint
realisation, all-coordinate/all-branch coverage, Lemma 5 order count, normal
crossings, or RLCT extraction.

## Residual Risks

This theorem counts only the strict offset values for one rising coordinate.
It does not construct Eq5 displayed vectors, prove source-label legality,
realise endpoints, aggregate over all coordinates, package all branches, prove
Lemma 5 order count, normal crossings, or RLCT extraction.
