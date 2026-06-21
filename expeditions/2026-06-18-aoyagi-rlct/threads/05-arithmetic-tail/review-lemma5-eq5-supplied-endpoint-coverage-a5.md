# Review - Eq5 supplied endpoint coverage split

Date: 2026-06-21.

Reviewer: Linnaeus, xhigh-effort read-only review.

Verdict: ACCEPT.

## Scope

Reviewed the current supplied endpoint coverage slice in
`Lemma5DisplayedVector.lean`, together with the reproduction and statement
card:

- `aoyagiLemma5_suppliedUpperLower_Eq5_offsets_eq_intervalValueSetNat_of_le_min`
- `aoyagiLemma5_suppliedEndpointCoverage_Eq5_offsets_split`

The review checked that this is finite supplied-data bookkeeping only and does
not cross the source-facing boundary for Aoyagi's displayed branch family.

## Findings

No blocking findings.

The two new Lean statements are accurate supplied-data bookkeeping.  The rising
theorem assumes explicit supplied upper and lower endpoint equalities and proves
only the finite-set interval fill, using the existing lower-plus-offset identity
and `Finset.insert_erase`.  It does not claim source-label legality,
terminality, chart coverage, branch-family coverage, pole order, normal
crossings, or RLCT extraction.

The `insert`/`erase` reasoning is sound.  The non-rising branch uses
`aoyagiLemma5IntervalExcess_le_pred_of_not_le_min` to reduce to the existing
upper-only wrapper.  The rising branch uses the supplied upper/lower endpoint
wrapper.  Thus the split is exactly an endpoint obligation split:

- outside the rising region, a supplied upper endpoint plus strict Eq5 offsets
  fills the same-coordinate interval;
- in the rising region, supplied upper and lower endpoints plus strict Eq5
  offsets fill the same-coordinate interval.

The reproduction matches the Lean boundary.  It states the endpoint-deficit
input, records the supplied upper/lower endpoint equalities, and derives the
same disjunction as the Lean split theorem.  The compressed paper calculation
inserting the lower endpoint is backed in Lean by the existing
`aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min`
wrapper, not by any hidden source assumption.

The naming and documentation are acceptable.  The word `coverage` is
consistently qualified by `supplied`, and the notes explicitly rule out treating
the result as Eq3/Eq4/Eq5 source legality or as all-coordinate source coverage.

## Downstream Caveat

The split theorem's left disjunct does not carry an explicit
`not (p <= a and p <= ell-a)` hypothesis.  This is fine for endpoint coverage,
but downstream code needing a branch classifier should add a separate
classifier theorem rather than infer non-rising merely by pattern matching on
the `Or`.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

and it passed.
