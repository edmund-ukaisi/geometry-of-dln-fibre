# Review - Lemma 5 Eq3 tail upper Eq5 coverage

Date: 2026-06-21.

Reviewer: Raman, xhigh-effort read-only review.

Verdict: ACCEPT.

## Scope

Reviewed the Eq3 ordinary-tail upper endpoint and Eq5 non-rising coverage
slice:

- `aoyagiLemma5Eq3_piecewise_tail_upperEndpoint_of_boundary_lt`
- `aoyagiLemma5_suppliedEq3TailUpper_Eq5_offsets_eq_intervalValueSetNat_of_boundary_lt`

The review covered the Lean statements and proofs, the reproduction, statement
card, and the expedition ledger/thread/synthesis updates.

## Findings

No blocking issues found.

The finite arithmetic is sound.  The guard `p < ell` puts `C.point p - 1` in
selected block `p` by `AoyagiSelectedCutpoints.leftEndpoint_mem_block`.  The
strict guard `ell-a+1 < p`, together with strict monotonicity of selected
cutpoints, proves

```text
C.point (ell-a+1)-1 < C.point p-1.
```

Thus the supplied Eq3 tail clause applies at this selected-block left
endpoint.  This exactly matches the `tail` field of the supplied
`AoyagiLemma5Eq3PiecewiseSourceVector` certificate.

The Eq5 coverage wrapper is correct.  The same strict guard implies
`not (p <= a and p <= ell-a)`, so the existing non-rising excess lemma applies.
The proof then uses the existing supplied-upper Eq5 interval-coverage theorem
with the Eq3 tail component value as the supplied upper endpoint.

The Lean statements and notes do not overclaim source-label legality,
own-source-label status, terminality, all-coordinate coverage, or the Lemma 5
order count.  The reproduction and statement card explicitly distinguish this
component-value result from source-label realisation, and the synthesis records
the source-scout warning that Aoyagi PDF pp. 26-27 do not prove
all-coordinate endpoint realisation, injection, or back-to-label coverage.

Naming and API risk are low.  The theorem names are long but consistent with
the surrounding supplied-endpoint API and explicitly record the
ordinary-tail/boundary-exclusion guard.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

from the Lean project root, and it passed.
