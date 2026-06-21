# Review - Lemma 5 Eq5 Offsets as Interval With Endpoints Erased

Reviewers: controller review; xhigh exact-diff reviewer.
Verdict: finite-set wrapper is source-safe.

## Findings

No issue was found in the controller check.

No issue was found by the xhigh exact-diff reviewer.

The wrapper uses only:

```text
aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min
```

The first identifies lower endpoint plus strict Eq5 offsets with the interval
after erasing the upper endpoint.  The second says the lower endpoint is not a
strict Eq5 offset.  The new theorem erases the lower endpoint from that
finite-set equality.

## Checks

Controller check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

passed before this note was updated.

Exact-diff reviewer checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check 375cfd3
```

both passed.  The controller also ran `lake build DLNFibre`; it passed with
only known pre-existing Core warnings.

## Residual Risks

This is not a displayed-vector construction or order-count theorem.  It keeps
the rising-region hypotheses explicit and does not claim that the erased
endpoints are realised by admissible vectors.
