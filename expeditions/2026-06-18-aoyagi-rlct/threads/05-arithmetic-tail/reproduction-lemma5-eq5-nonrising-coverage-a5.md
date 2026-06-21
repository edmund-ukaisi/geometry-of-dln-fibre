# Reproduction - Eq5 non-rising interval coverage

Date: 2026-06-21.

Scope: finite interval bookkeeping for Aoyagi Lemma 5 equation `(5)` offset
values outside the strictly rising part of the interval-size profile.  This
does not construct Aoyagi's displayed source vectors, prove source-label
legality, terminal `tilde t=0`, chart coverage, pole order, normal crossings,
or RLCT extraction.

## Interval Coordinates

For a coordinate `p`, write

```text
L_p = Htilde_p
U_p = Htilde'_p
e_p = U_p - L_p = aoyagiLemma5IntervalExcess ell a p.
```

The same-coordinate interval value set is

```text
I_p = { L_p, L_p+1, ..., U_p }.
```

Equivalently, in decreasing coordinates from the upper endpoint,

```text
I_p = { U_p - alpha | 0 <= alpha <= e_p }.
```

The upper endpoint is `alpha=0`; the lower endpoint is `alpha=e_p`.

## Equation (5) Offset Set

The strict equation `(5)` offset set in Lean is

```text
E_p = { U_p - alpha | 1 <= alpha <= min(e_p, p-1) }.
```

Thus `E_p` always omits the upper endpoint because `alpha=0` is excluded.

In the rising region `e_p=p`, equation `(5)` stops at `alpha=p-1`, so the lower
endpoint `alpha=e_p` is also omitted.  This is the already formalised
rising-region result: Eq5 offsets equal the interval with both endpoints
erased, and adding the Eq4 lower endpoint gives the interval with the upper
endpoint erased.

In the complementary finite situation where

```text
e_p <= p-1,
```

the upper bound in the Eq5 offset set becomes exactly `e_p`, so

```text
E_p = { U_p - alpha | 1 <= alpha <= e_p }
    = I_p \ { U_p }.
```

No lower endpoint needs to be supplied separately in this case; Eq5 already
reaches it.

## Supplied Upper Endpoint

If some supplied branch certificate has own-coordinate value `U_p`, then

```text
{U_p} union E_p = I_p.
```

This is a useful finite-set wrapper for plateau/falling coordinates.  It still
does not say that equation `(3)` or another printed branch legally supplies
the upper endpoint.

## Eq3-Shaped Plateau Wrapper

The existing Eq3-shaped piecewise certificate has component value `U_p` on
block `p` under `1<=p` and `p<=ell-a`.  Therefore, in the plateau subcase
where `a<p` and `p<=ell-a`, we can instantiate the supplied-upper wrapper:
`e_p<=a<p`, hence `e_p<=p-1`, and the Eq3-shaped component plus Eq5 offsets
fill the interval.

This remains conditional on the supplied Eq3-shaped piecewise certificate and
does not prove source-label legality or terminality for the Eq3 branch.

## Formalisation Boundary

The Lean slice should add:

```text
aoyagiLemma5Eq5_upperEndpoint_not_mem_offsetValueSet
aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred
aoyagiLemma5_suppliedUpper_Eq5_offsets_eq_intervalValueSetNat_of_excess_le_pred
aoyagiLemma5_suppliedEq3Upper_Eq5_offsets_eq_intervalValueSetNat_of_plateau
aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_plateau
```

This is a non-rising finite-set bridge below the full Lemma 5 branch-family
realisation.  It must not be described as an all-coordinate source coverage
proof.
