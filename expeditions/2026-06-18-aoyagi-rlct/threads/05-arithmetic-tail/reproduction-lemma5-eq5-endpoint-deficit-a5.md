# Reproduction - Eq5 endpoint deficit split

Date: 2026-06-21.

Scope: finite endpoint-deficit bookkeeping for Aoyagi Lemma 5 equation `(5)`.
This does not construct Aoyagi's displayed source vectors, prove source-label
legality, terminal `tilde t=0`, chart coverage, pole order, normal crossings,
or RLCT extraction.

## Interval and Offset Counts

At coordinate `p`, write

```text
e_p = aoyagiLemma5IntervalExcess ell a p.
```

The same-coordinate interval has size

```text
|I_p| = 1 + e_p.
```

The strict equation `(5)` offset set has size

```text
|E_p| = min(e_p, p-1),
```

because Eq5 uses offsets

```text
1 <= alpha <= min(e_p, p-1).
```

Thus Eq5 always has an upper-endpoint deficit, corresponding to the excluded
offset `alpha=0`.

## Rising vs Non-Rising

The interval excess satisfies

```text
e_p <= p.
```

Under `a<=ell`, equality `e_p=p` is exactly the rising condition

```text
p <= a and p <= ell-a.
```

Indeed, if both inequalities hold, then the four arguments of the nested
minimum defining `e_p` are all at least `p`, so `e_p=p`.  Conversely, if the
nested minimum is `p`, then in particular `p<=a` and `p<=ell-a`.

For `1<=p`, the complement of the rising case gives

```text
e_p <= p-1.
```

Therefore:

- rising case: `|E_p| = p-1 = e_p-1`, so
  `|I_p| = |E_p| + 2`;
- non-rising case: `|E_p| = e_p`, so
  `|I_p| = |E_p| + 1`.

Equivalently,

```text
|I_p| = |E_p| + 1
  + if 1<=p and p<=a and p<=ell-a then 1 else 0.
```

## Set-Level Split

The set equalities match the same endpoint deficit.

In the non-rising case `e_p<=p-1`, the previous slice proved

```text
E_p = I_p \ {U_p}.
```

In the rising case `p<=a` and `p<=ell-a`, the previous rising-region theorem
proved

```text
E_p = I_p \ {U_p,L_p}.
```

Thus every coordinate is in one of the following finite bookkeeping cases:

```text
E_p = I_p.erase U_p
```

or

```text
p<=a, p<=ell-a, and E_p = (I_p.erase U_p).erase L_p.
```

This split is useful because it states exactly which endpoint values remain
to be supplied by non-Eq5 branches in each region.

## Formalisation Boundary

The Lean slice should add:

```text
aoyagiLemma5IntervalExcess_eq_self_iff_le_min
aoyagiLemma5IntervalExcess_le_pred_of_not_le_min
aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit
aoyagiLemma5Eq5_offsets_endpointDeficit_split
```

These are finite arithmetic and set identities only.  They must not be read as
source-backed branch-family coverage or as Aoyagi Lemma 5's order count.
