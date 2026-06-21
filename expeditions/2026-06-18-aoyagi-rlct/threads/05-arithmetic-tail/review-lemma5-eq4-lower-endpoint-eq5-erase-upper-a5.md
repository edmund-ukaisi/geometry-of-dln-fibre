# Review - Lemma 5 Eq4 lower endpoint and Eq5 erase-upper set

Reviewers: controller review; xhigh exact-diff reviewer.
Verdict: finite-set wrapper is source-safe.

## Findings

No issue was found in the controller check.

No issue was found by the xhigh exact-diff reviewer.

The wrapper uses only:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
```

The first supplies `T(C.point p-1)=Htilde_p`; the second supplies the finite
Eq5 erase-upper equality for the abstract lower endpoint.  The result is only
their substitution.

## Checks

Controller check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

passed before this note was updated.

Exact-diff reviewer checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check
```

both passed.  The reviewer also checked that the wrapper uses only the existing
Eq4 own-coordinate theorem and the existing Eq5 erase-upper finite-set equality,
and that the docs keep the nonclaims explicit.

## Residual Risks

This is not a displayed-vector construction or order-count theorem.  It still
leaves the upper endpoint erased, keeps the rising-region hypotheses explicit,
and depends on the supplied Eq4 piecewise certificate.
