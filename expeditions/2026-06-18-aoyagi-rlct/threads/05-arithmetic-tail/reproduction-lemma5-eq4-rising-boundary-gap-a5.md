# Reproduction - Lemma 5 Eq4 rising-boundary gap

Date: 2026-06-21.

Scope: one-coordinate obstruction at the rising boundary `p=a`.  This records
that Eq5 still has the rising lower-endpoint deficit at `p=a` when
`1<=a<=ell-a`, but the repaired Eq4 source-shaped certificate cannot exist at
that coordinate because its selected-index guard requires `p+1<=a`.

This does not construct Aoyagi's displayed vectors, prove source-label
legality, chart coverage, all-coordinate branch-family coverage, pole order,
normal crossings, or RLCT extraction.

## Source Inventory

Aoyagi Lemma 5 equation `(4)` is represented in Lean by a supplied certificate
`AoyagiLemma5Eq4PiecewiseSourceVector`.  The repaired source-index guard in
that certificate is

```text
p+1 <= a.
```

This is the guard that makes the printed cutoff `S_(p+ell-a+2)` lie in the
selected list.  The arithmetic equivalence is already recorded as
`aoyagiLemma5Eq4_selectedIndexGuard_iff`.

Eq5's strict offsets at a rising coordinate miss both endpoints:

```text
Eq5Offsets_p = (IntervalValueSet_p.erase upper_p).erase lower_p
```

under `1<=p`, `p<=a`, and `p<=ell-a`.

## Pen-And-Paper Derivation

Assume

```text
a <= ell,    1 <= a,    a <= ell-a.
```

Set `p=a`.  Then the rising hypotheses for Eq5 are

```text
1 <= p,    p <= a,    p <= ell-a,
```

because `p=a`, `1<=a`, and `a<=ell-a`.  Therefore the existing Eq5
endpoint-deficit theorem gives

```text
Eq5Offsets_a
  = (IntervalValueSet_a.erase Htilde'_a).erase Htilde_a.
```

Thus Eq5 alone does not contain the lower endpoint at coordinate `a`.

Now suppose an Eq4 piecewise certificate existed at the same coordinate
`p=a`.  Its guard would give

```text
p+1 <= a.
```

Substituting `p=a` gives

```text
a+1 <= a,
```

which is impossible in `Nat`.  Hence no source-shaped Eq4 certificate of the
current repaired form exists at `p=a`.

This is distinct from the existing `p+1=a` terminal Eq4 case.  Here the
coordinate is `p=a`, so the obstruction is that the Eq4 guard itself fails,
while Eq5 is still in the rising region when `a<=ell-a`.

## Lean Targets

```text
aoyagiLemma5Eq4_no_piecewiseSourceVector_of_not_indexGuard
aoyagiLemma5Eq4_no_piecewiseSourceVector_of_eq_a
aoyagiLemma5Eq5_risingBoundary_eq_a_noEq4LowerEndpoint
```

## Kill Conditions

- Keep Eq4 as a supplied source-shaped certificate, not a constructed vector.
- Do not identify this with the existing `p+1=a` terminal Eq4 obstruction.
- Keep the rising hypotheses `1<=a` and `a<=ell-a` explicit for the Eq5
  erased-endpoints equality.
- Do not infer that Eq4 supplies the lower endpoint at `p=a`.
- Do not infer source-label legality, all-coordinate endpoint realisation,
  injection, back-to-label coverage, Lemma 5 order count, normal crossings, or
  RLCT extraction.
