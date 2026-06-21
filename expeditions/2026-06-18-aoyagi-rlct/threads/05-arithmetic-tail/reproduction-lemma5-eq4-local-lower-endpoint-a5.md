# Reproduction - Lemma 5 Eq4 Local Lower Endpoint

Status: local finite-set wrapper; ready for a narrow Lean theorem.

This note sharpens the existing Eq4 lower-endpoint wrappers.  The older wrapper
combined the lower endpoint with source-label legality, so it required the
global selected-width sum and Definition 3 source inequalities.  The calculation
below records the smaller finite-set fact: in the rising window, a supplied
Eq4 piecewise certificate already gives the lower chain endpoint at its own
coordinate.

## Local Window

Let `p` be a positive selected-coordinate index.  The Eq4 repaired guard is

```text
p + 1 <= a.
```

The Eq5 lower-endpoint deficit occurs in the rising region

```text
p <= a,
p <= ell-a.
```

Since Eq4's guard already implies `p <= a`, the relevant overlap is

```text
1 <= p,
p + 1 <= a,
p <= ell-a.
```

The supplied Eq4 piecewise certificate carries `p+1<=a` and `a<=ell`; the Lean
theorems therefore ask only for `1<=p`, `p<=ell-a`, and the supplied
certificate.

## Own Coordinate Value

At the own coordinate, the source index is the left endpoint of block `p`,
namely `C.point p - 1`.  Because `p+1<=a<=ell`, we have `p<ell`, so this left
endpoint belongs to block `p`.

Eq4's prefix branch clause gives

```text
T4(C.point p - 1) = Htilde'_p - p.
```

In the rising window, the Htilde gap at coordinate `p` is exactly `p`, so

```text
Htilde'_p - p = Htilde_p.
```

Therefore

```text
T4(C.point p - 1) = Htilde_p.
```

This is only the lower endpoint value.  It does not assert that
`Htilde_p+1` is a legal source label.

## Eq5 Lower Deficit

In the same rising window, Eq5's strict offsets are exactly the same-coordinate
interval with both endpoints erased:

```text
Eq5Offsets_p = (Interval_p.erase Htilde'_p).erase Htilde_p.
```

Inserting the Eq4 own-coordinate value therefore gives

```text
insert T4(C.point p - 1) Eq5Offsets_p
  = Interval_p.erase Htilde'_p.
```

Consequently the inserted set has cardinality one larger than the strict Eq5
offset set.

If a separate upper endpoint value is supplied,

```text
Tupper(C.point p - 1) = Htilde'_p,
```

then inserting the upper endpoint as well fills the full interval.

If the upper endpoint is supplied by an Eq3-shaped certificate, the same
finite-set conclusion follows, again without source-label legality for the
upper component.

## Boundary Caveats

- At `p=a`, Eq5 may still be in the rising region, but Eq4's repaired guard
  would require `a+1<=a`; this is the recorded rising-boundary gap.
- At `p+1=a`, Eq4 can supply the lower own-coordinate value when `1<=p` and
  `p<=ell-a`.  Separately, Eq4's special boundary collides with the terminal
  selected endpoint; terminal extension still needs its own last-width
  compatibility condition.
- If `ell-a < p`, Eq4's own-coordinate value may exist under its guard, but
  Eq5 no longer has a lower-endpoint deficit.  The Eq5 inventory is then the
  erase-upper case.

## Lean Targets

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_lowerEndpoint_of_le_min
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_piecewise
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_piecewise
aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_piecewise
aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_eq_intervalValueSetNat
```

## Kill Conditions

- Do not infer source-label legality from the lower endpoint equality.
- Do not claim Eq4 exists at `p=a`.
- Do not treat the `p+1=a` terminal-collision compatibility as solved.
- Do not claim all-coordinate branch-family coverage, injection,
  back-to-label coverage, pole order, normal crossings, or RLCT extraction.

## Nonclaims

- No displayed source vector is constructed.
- No source label is proved legal.
- No full Lemma 5 chart family is constructed.
- No terminal minimizer exactness or pole-order theorem is proved.
