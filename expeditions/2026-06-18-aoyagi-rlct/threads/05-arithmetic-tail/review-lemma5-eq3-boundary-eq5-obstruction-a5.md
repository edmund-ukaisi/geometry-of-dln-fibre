# Review - Lemma 5 Eq3 boundary Eq5 obstruction

Date: 2026-06-21.

Reviewer: Feynman, xhigh-effort read-only review.

Verdict: ACCEPT.

## Scope

Reviewed the Eq3 boundary obstruction against Eq5 endpoint coverage:

- `aoyagiLemma5Eq3_boundaryValue_ne_upperEndpoint`
- `aoyagiLemma5Eq3_boundaryValue_not_mem_Eq5_offsets`
- `aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat`
- `aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat_of_eq_boundary`

The review checked the Lean proof, reproduction, statement card, and
expedition ledger/thread/synthesis/claims/priorities updates.

## Findings

No blocking findings.

The Eq3 supplied boundary clause is exactly the source of
`Htilde'_(ell-a+1)+1`, so the value-level non-equality theorem is narrow and
sound.  The set-level obstruction is also sound: if the inserted set were the
same-coordinate interval, the inserted boundary value would belong to that
interval, contradicting the existing Eq3 boundary interval obstruction.

The Eq5-offset nonmembership theorem uses the right dependency:
`aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat` places strict Eq5
offsets inside the same-coordinate interval, while the Eq3 boundary value is
outside that interval.

The external-`p` wrapper is only a restatement under `p=ell-a+1` and adds no
coverage claim.  The docs consistently describe this as an obstruction, not
endpoint realisation or Lemma 5 completion.

The reviewer also checked the local Aoyagi PDF extraction around pp. 26-27:
Eq3 has the special line `Htilde'_(ell-a+1)+1`, and Eq5 is the strict-offset
family.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

from the Lean project root, and it passed.
