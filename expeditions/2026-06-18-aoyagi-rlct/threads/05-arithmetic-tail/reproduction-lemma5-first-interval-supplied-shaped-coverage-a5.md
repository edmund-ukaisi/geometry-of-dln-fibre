# Reproduction - Lemma 5 First-Interval Supplied Shaped Coverage

Status: checked finite-set/API wrapper.

This note records the first-coordinate finite-set coverage obtained by
combining a supplied Eq4 lower endpoint, a separately supplied Eq3-shaped upper
endpoint, and the strict Eq5 offset set.  It does not construct the displayed
branch family.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, displays Eq4 and Eq5 pieces meeting the first
same-coordinate interval:

- Eq4 with `p=1` supplies the lower endpoint value `Htilde_1`.
- Eq5 supplies strict offset values between the lower and upper endpoints.

The printed equation `(3)` explicitly excludes the label
`(S_2-1,Htilde'_1+1)`.  Therefore the upper endpoint used in this Lean wrapper
is not claimed to be supplied by the printed Eq3 branch.  It is a separately
supplied Eq3-shaped certificate whose own-coordinate theorem has the same
upper-endpoint value.

The existing Lean theorem
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min`
already proves that the supplied Eq4 lower endpoint plus the strict Eq5 offset
set is:

```text
(aoyagiHtildeIntervalValueSetNat ell a M m 1).erase Htilde'_1.
```

## Reproduction

Assume a supplied Eq4 certificate at `p=1`.  The Eq4/Eq5 finite-set equality
gives:

```text
insert (T4 (C.point 1 - 1))
  (aoyagiLemma5Eq5OffsetValueSet ell a 1 M m)
= (aoyagiHtildeIntervalValueSetNat ell a M m 1).erase
    (aoyagiHtildeUpperNat ell a M m 1).
```

Assume a separately supplied Eq3-shaped certificate.  Its own-coordinate
theorem gives:

```text
T3 (C.point 1 - 1) = aoyagiHtildeUpperNat ell a M m 1.
```

The upper endpoint belongs to the same-coordinate interval, so `Finset`
bookkeeping gives:

```text
insert Htilde'_1
  ((aoyagiHtildeIntervalValueSetNat ell a M m 1).erase Htilde'_1)
= aoyagiHtildeIntervalValueSetNat ell a M m 1.
```

Substituting the supplied upper-endpoint and Eq4 lower-endpoint equalities
proves the target finite-set equality.

## Lean Target

```text
aoyagiLemma5_suppliedEq3Upper_Eq4_firstInterval_insertOwnCoordinates_eq_intervalValueSetNat
```

## Kill Conditions

- Keep the Eq3-shaped upper-endpoint and Eq4 piecewise certificates supplied.
- Keep the explicit slack for the Eq3-shaped upper-endpoint wrapper.
- Keep the first-interval rising-region guard `1 <= ell-a`.
- Do not claim that printed Eq3 supplies the excluded first-interval upper
  endpoint label.
- Do not infer all intervals or all branches from this first-interval result.
- Do not infer displayed-vector construction, source-label legality,
  exponent certificates, terminality, Lemma 5 order count, normal crossings,
  or RLCT extraction.
