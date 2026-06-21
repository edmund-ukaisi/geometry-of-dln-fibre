# Reproduction - Lemma 5 Eq4 Lower Plus Eq5 Offset Count

Status: checked finite count wrapper.

This note records the source-facing cardinality consequence of inserting the
supplied equation `(4)` lower endpoint into the strict equation `(5)` offset
set.  It does not construct displayed vectors.

## Source

Aoyagi Lemma 5, PDF pp. 26-27:

- Equation `(4)` supplies a lower endpoint value at the own coordinate:
  `T(C.point p - 1) = Htilde_p`.
- Equation `(5)` supplies strict offsets below the upper endpoint.

The already-formalised count-side theorem proves that, in the rising region,
the abstract lower endpoint plus the Eq5 strict offsets has cardinality equal
to the interval excess.

## Reproduction

Assume the rising-region guards:

```text
a <= ell,  1 <= p,  p <= a,  p <= ell-a.
```

The supplied Eq4 piecewise certificate and source-selected arithmetic give:

```text
T(C.point p - 1) = Htilde_p.
```

Therefore:

```text
card(insert (T(C.point p - 1)) Eq5Offsets)
  = card(insert Htilde_p Eq5Offsets).
```

The existing abstract count theorem gives:

```text
card(insert Htilde_p Eq5Offsets) = excess_p.
```

In the rising region:

```text
excess_p = p.
```

The strict Eq5 rising count gives:

```text
card(Eq5Offsets) = p-1.
```

Thus:

```text
card(insert (T(C.point p - 1)) Eq5Offsets)
  = card(Eq5Offsets) + 1.
```

## Lean Target

```text
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_le_min
```

## Kill Conditions

- Keep the supplied Eq4 piecewise certificate and repaired source guards.
- Do not infer source-label legality.
- Do not construct Eq4 or Eq5 displayed vectors.
- Do not infer upper endpoint realisation, all-coordinate coverage,
  all-branch packaging, Lemma 5 order count, normal crossings, or RLCT
  extraction.
