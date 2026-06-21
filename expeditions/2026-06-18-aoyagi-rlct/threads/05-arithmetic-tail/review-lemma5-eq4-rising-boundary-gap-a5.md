# Review - Lemma 5 Eq4 rising-boundary gap

Date: 2026-06-21.

Reviewer: Planck, xhigh-effort read-only review.

Verdict: ACCEPT.

## Scope

Reviewed the Eq4 rising-boundary gap slice:

- `aoyagiLemma5Eq4_no_piecewiseSourceVector_of_not_indexGuard`
- `aoyagiLemma5Eq4_no_piecewiseSourceVector_of_eq_a`
- `aoyagiLemma5Eq5_risingBoundary_eq_a_noEq4LowerEndpoint`

The review checked the Lean proof, reproduction, statement card, and
expedition ledger/thread/synthesis/claims/priorities updates.

## Findings

No blocking findings.

The Lean slice is sound and narrow.  The Eq4 certificate's repaired guard is
`p+1<=a`, and the two nonexistence lemmas are direct consequences of that
guard.  The combined theorem correctly specializes the existing Eq5
erased-endpoints theorem at `p=a` and pairs it with the Eq4 guard-failure
obstruction.

The docs correctly distinguish this `p=a` guard-failure gap from the existing
`p+1=a` terminal Eq4 case.  Overclaim guards are explicit: the slice is a gap
record, not a lower-endpoint construction or Lemma 5 endpoint-realisation
theorem.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check
```

Both passed.
