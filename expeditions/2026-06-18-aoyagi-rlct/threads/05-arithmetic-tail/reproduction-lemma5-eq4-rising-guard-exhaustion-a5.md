# Reproduction - Lemma 5 Eq4 rising-guard exhaustion

Date: 2026-06-21.

Scope: elementary guard arithmetic for Aoyagi Lemma 5 equation `(4)`.  In the
rising-side range `p<=a`, failure of the repaired Eq4 guard `p+1<=a` is
exactly the already recorded boundary `p=a`.

This does not construct the equation `(4)` source vector, fill an Eq5 lower
endpoint, prove source-label legality, prove chart coverage, count pole order,
prove normal crossings, or extract RLCT.

## Source Inventory

Aoyagi's displayed equation `(4)` on PDF p. 27 is stated for

```text
s = S_(j0+1)-1,  k = Htilde_(j0)+1,  j0 <= a.
```

The final branch of the displayed source vector refers to the cutoff

```text
S_(j0+ell-a+2)-1.
```

For this selected cutpoint to be in the selected list
`S_1,...,S_(ell+1)`, with Lean's coordinate `p=j0`, the repaired index guard
is

```text
p + (ell-a) + 2 <= ell + 1.
```

The existing Lean theorem `aoyagiLemma5Eq4_selectedIndexGuard_iff` rewrites
this raw selected-index guard as

```text
p+1 <= a.
```

Thus Aoyagi's printed hypothesis `p<=a` is one unit weaker than the repaired
source-index guard at the boundary `p=a`.

## Pen-And-Paper Derivation

Assume the rising-side hypothesis

```text
p <= a.
```

For natural numbers, failure of the repaired guard is

```text
not (p+1 <= a).
```

Equivalently, `a < p+1`, hence `a <= p`.  Combining this with `p<=a` gives
`p=a`.

Conversely, if `p=a`, then the repaired guard would be

```text
a+1 <= a,
```

which is impossible.  Therefore, under `p<=a`,

```text
not (p+1 <= a)  iff  p=a.
```

Using `aoyagiLemma5Eq4_selectedIndexGuard_iff`, the same statement can be
phrased in raw selected-index form: under `a<=ell` and `p<=a`,

```text
not (p + (ell-a) + 2 <= ell+1)  iff  p=a.
```

Finally, `AoyagiLemma5Eq4PiecewiseSourceVector` carries the field

```text
indexGuard : p+1 <= a.
```

Thus, if `p<=a` and the guard fails, then `p=a` and no supplied Eq4-piecewise
source vector of that repaired shape exists.  The nonexistence conclusion is
only a guard-failure consequence.

## Lean Targets

```text
aoyagiLemma5Eq4_risingGuardFailure_iff_eq_a
aoyagiLemma5Eq4_selectedIndexGuardFailure_iff_eq_a
aoyagiLemma5Eq4_risingGuardFailure_eq_a_and_no_piecewiseSourceVector
```

## Kill Conditions

- Do not state `not Eq4PiecewiseSourceVector iff p=a`; other obstructions may
  exist.
- Do not identify this with the guard-success boundary `p+1=a`.
- Do not claim Eq4 supplies the missing lower endpoint at `p=a`.
- Do not claim Eq4 vector existence from guard success.
- Do not infer source-label legality, injection, back-to-label coverage,
  Lemma 5 order count, normal crossings, or RLCT extraction.
