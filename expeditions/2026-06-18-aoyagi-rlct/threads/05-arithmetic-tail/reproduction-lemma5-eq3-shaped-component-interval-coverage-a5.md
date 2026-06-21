# Reproduction - Lemma 5 Eq3-Shaped Component Interval Coverage

Status: checked finite-set/API wrapper.

This note instantiates the supplied-upper interval coverage wrapper with the
component value of a supplied Eq3-shaped piecewise certificate.  It does not
turn that component into a legal source label.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, displays an Eq3-shaped piecewise vector whose
ordinary upper branch has value `Htilde'_p` on the selected block `p` in the
rising range `1 <= p <= ell-a`.  The already-formalised record
`AoyagiLemma5Eq3PiecewiseSourceVector` stores this branch value as supplied
piecewise data.

The source-fidelity boundary is important: this theorem uses only the
component value of the supplied Eq3-shaped certificate.  It does not claim that
the component is the own coordinate of a source label, nor that the label
`Htilde'_p+1` is legal.

## Reproduction

Assume `1 <= p` and `p <= ell-a`.  The supplied Eq3-shaped piecewise
certificate gives, on block `p`,

```text
T3 (C.point p - 1) = aoyagiHtildeUpperNat ell a M m p.
```

The previously proved supplied-upper theorem says that any supplied upper
endpoint equality, together with a supplied Eq4 lower endpoint and strict Eq5
offsets, fills the interval:

```text
insert upper
  (insert lower offsets_p)
= aoyagiHtildeIntervalValueSetNat ell a M m p.
```

Substituting the Eq3-shaped component value for the supplied upper endpoint
gives:

```text
insert (T3 (C.point p - 1))
  (insert (T4 (C.point p - 1))
    (aoyagiLemma5Eq5OffsetValueSet ell a p M m))
= aoyagiHtildeIntervalValueSetNat ell a M m p.
```

## Lean Targets

```text
aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap
aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat
```

## Kill Conditions

- Keep the Eq3-shaped and Eq4 piecewise certificates supplied.
- Keep the rising-region guards `1 <= p`, `p <= a`, and `p <= ell-a`
  explicit.
- Do not infer source-label legality or introduced-label status for the Eq3
  component.
- Do not claim displayed-vector construction, all-interval coverage,
  all-branch coverage, Lemma 5 order count, normal crossings, or RLCT
  extraction.
