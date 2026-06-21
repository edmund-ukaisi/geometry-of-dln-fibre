# Statement Card - A5 Lemma 5 First-Interval Supplied Shaped Coverage

## Lean Name

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEq3Upper_Eq4_firstInterval_insertOwnCoordinates_eq_intervalValueSetNat`

## Claim

For the first same-coordinate interval, a supplied Eq4 lower endpoint and a
separately supplied Eq3-shaped upper endpoint fill the two endpoints missing
from the strict Eq5 offset set.  Under the rising-region guard `1 <= ell-a`,
this is not a claim about the printed Eq3 branch: printed equation `(3)`
excludes the label `(S_2-1,Htilde'_1+1)`.

```text
insert (T3 (C.point 1 - 1))
  (insert (T4 (C.point 1 - 1))
    (aoyagiLemma5Eq5OffsetValueSet ell a 1 M m))
= aoyagiHtildeIntervalValueSetNat ell a M m 1.
```

## Inputs

- Supplied Eq3-shaped piecewise source-vector certificate for the upper
  endpoint value.
- Supplied Eq4 piecewise source-vector certificate with `p=1`.
- Source selected-width sum and strict source inequalities.
- Explicit slack `W_1 + 2 <= M` for the Eq3-shaped upper endpoint wrapper.
- First-interval rising-region guard `1 <= ell-a`.

## Proves

Only a finite-set equality for the first interval's supplied-shaped endpoint
values and strict Eq5 offset set.

## Does Not Prove

- Construction of the Eq3, Eq4, or Eq5 displayed vectors.
- Coverage for all intervals or all branch families.
- Source-label legality, exponent certificates, terminality, admissibility,
  chart sequence, Lemma 5 order count, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(4)` and `(5)`, PDF pp. 26-27, plus the
already-formalised finite-set equality identifying Eq4's lower endpoint plus
Eq5 strict offsets with the interval after erasing the upper endpoint.  The
printed equation `(3)` excludes the label `(S_2-1,Htilde'_1+1)`, so the upper
endpoint in this theorem is a separately supplied Eq3-shaped certificate, not
a claim about the printed Eq3 branch.
