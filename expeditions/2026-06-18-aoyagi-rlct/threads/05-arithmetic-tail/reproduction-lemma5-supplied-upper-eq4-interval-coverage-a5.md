# Reproduction - Lemma 5 Supplied Upper and Eq4 Interval Coverage

Status: checked finite-set/API wrapper.

This note records the p-general finite-set coverage obtained from a supplied
upper endpoint value, a supplied Eq4 lower endpoint, and the strict Eq5 offset
set.  It does not identify the upper endpoint with a printed Eq3 source label.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, counts same-coordinate intervals

```text
{H : Htilde_p <= H <= Htilde'_p}.
```

The already-formalised Eq5 finite-set theorem says that, in the rising range
`1 <= p`, `p <= a`, and `p <= ell-a`, the strict Eq5 offset set together with
the lower endpoint is the interval with the upper endpoint erased.  The
already-formalised Eq4 wrapper replaces that lower endpoint by the supplied
Eq4 own-coordinate value.

This wrapper keeps the upper endpoint as a separate supplied equality

```text
Tupper(C.point p - 1) = Htilde'_p.
```

It deliberately does not claim that any printed Eq3 branch supplies this value,
nor that the value is a legal source label.

## Reproduction

Assume a supplied Eq4 certificate at coordinate `p`.  The existing Eq4/Eq5
finite-set equality gives:

```text
insert (T4 (C.point p - 1))
  (aoyagiLemma5Eq5OffsetValueSet ell a p M m)
= (aoyagiHtildeIntervalValueSetNat ell a M m p).erase
    (aoyagiHtildeUpperNat ell a M m p).
```

Assume separately:

```text
Tupper (C.point p - 1) = aoyagiHtildeUpperNat ell a M m p.
```

The upper endpoint belongs to the same-coordinate interval, so

```text
insert Htilde'_p
  ((aoyagiHtildeIntervalValueSetNat ell a M m p).erase Htilde'_p)
= aoyagiHtildeIntervalValueSetNat ell a M m p.
```

Substituting the supplied upper endpoint equality proves:

```text
insert (Tupper (C.point p - 1))
  (insert (T4 (C.point p - 1))
    (aoyagiLemma5Eq5OffsetValueSet ell a p M m))
= aoyagiHtildeIntervalValueSetNat ell a M m p.
```

## Lean Target

```text
aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_le_min
```

## Kill Conditions

- Keep the upper endpoint equality supplied.
- Keep the Eq4 piecewise certificate supplied.
- Keep the rising-region guards `1 <= p`, `p <= a`, and `p <= ell-a`
  explicit.
- Do not claim printed Eq3 supplies the upper endpoint.
- Do not claim source-label legality, introduced-label status, terminality,
  displayed-vector construction, all-interval coverage, all-branch coverage,
  Lemma 5 order count, normal crossings, or RLCT extraction.
