# Reproduction - Lemma 5 Eq3/Eq4 Interval Cardinality

Status: checked finite count wrapper.

This note records cardinality consequences of the supplied Eq3-shaped upper
component, supplied Eq4 lower endpoint, and strict Eq5 offset set filling one
same-coordinate interval.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, counts the interval

```text
{H : Htilde_p <= H <= Htilde'_p}
```

and displays Eq3/Eq4/Eq5 branch forms intended to account for the endpoint and
strict-offset values.  The current Lean theorem uses only previously supplied
one-coordinate branch certificates.

## Reproduction

The existing supplied interval-coverage theorem says:

```text
insert Eq3UpperComponent (insert Eq4Lower Eq5Offsets)
  = aoyagiHtildeIntervalValueSetNat ell a M m p.
```

Taking cardinalities and using the interval-cardinality theorem gives:

```text
card(insert Eq3UpperComponent (insert Eq4Lower Eq5Offsets))
  = aoyagiLemma5IntervalSize ell a p.
```

In the rising region:

```text
1 <= p,  p <= a,  p <= ell-a.
```

The interval size is `p+1`, and the strict Eq5 offset count is `p-1`.
Therefore:

```text
card(insert Eq3UpperComponent (insert Eq4Lower Eq5Offsets))
  = card(Eq5Offsets) + 2.
```

This records that, under supplied one-coordinate certificates, the two
endpoints contribute the two values missing from the strict-offset count.

## Lean Targets

```text
aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_card_eq_intervalSize
aoyagiLemma5_suppliedEq3Upper_Eq4_insertComponents_card_eq_offsetCard_add_two
```

## Kill Conditions

- Do not call the supplied Eq3-shaped component a printed Eq3 source branch.
- Do not infer Eq3 or Eq4 source-label legality.
- Do not construct displayed vectors.
- Do not aggregate over all coordinates or all branches.
- Do not prove Lemma 5 order count, normal crossings, or RLCT extraction.
