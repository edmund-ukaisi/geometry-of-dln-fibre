# Review - Lemma 5 First-Interval Supplied Shaped Coverage

Reviewers: controller review; Erdos the 2nd exact-diff xhigh review.
Verdict: PASS after repair.

## Findings

Initial exact-diff review found that the Lean theorem was formally conditional,
but the prose presented the first-interval upper endpoint as if it were
source-backed by the printed Eq3 branch.  The printed equation `(3)` excludes
`(S_2-1,Htilde'_1+1)`, so this must be stated as a separately supplied
Eq3-shaped upper endpoint.

The wrapper uses only:

```text
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min
aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
Finset.insert_erase
```

Repair status: theorem/doc names and prose were changed to say separately
supplied Eq3-shaped upper endpoint, and the source exclusion is now recorded
next to the claim.  The second exact-diff xhigh review passed.

## Checks

Controller checks completed so far:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
cd lean && scripts/sorries
git diff --check
cd lean && lake build DLNFibre
```

The full `DLNFibre` build completed successfully, with only pre-existing Core
warnings.

## Residual Risks

This is only first-interval finite-set coverage for supplied branch
certificates.  It is not all-interval coverage, displayed-vector construction,
source-label legality, exponent-certificate data, terminality, chart coverage,
Lemma 5 order count, normal crossings, or RLCT extraction.
