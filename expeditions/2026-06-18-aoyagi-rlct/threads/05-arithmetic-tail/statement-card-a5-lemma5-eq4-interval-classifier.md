# Statement card - A5 Lemma 5 equation (4) interval classifier

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_iff_two_mul_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_of_two_mul_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_not_mem_intervalValueSetNat_of_lt_two_mul`

## Statement

For a supplied Aoyagi Lemma 5 equation `(4)` branch certificate, assume the
strict boundary case

```text
1 <= p,  p+1 < a,  p <= ell-a.
```

Then the special boundary value

```text
T(C.point (p+(ell-a)+1)-1)
```

belongs to the Nat-indexed same-coordinate interval value set at coordinate
`p+(ell-a)` if and only if

```text
2*p <= a+1.
```

## Proved

- The supplied equation `(4)` boundary value is classified against
  `aoyagiHtildeIntervalValueSetNat ell a M m (p+(ell-a))`.
- Balanced case: `2*p <= a+1` implies membership.
- Unbalanced case: `a+1 < 2*p` implies nonmembership.

## Assumed

- A supplied equation `(4)` piecewise branch certificate.
- Strict boundary/range guards `1<=p`, `p+1<a`, and `p<=ell-a`.

## Cited

- None in Lean. This is finite integer and interval-set arithmetic.

## Deferred

- Construction or existence of the displayed vector.
- Terminal `tilde t=0`.
- Case 1(2) chart sequence, introduced-label status, vector admissibility,
  Lemma 5 order count, normal crossings, and RLCT extraction.
- Any uniform equation `(4)` interval obstruction.

## Verification

- From `lean/`:
  `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
