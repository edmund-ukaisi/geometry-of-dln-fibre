# Pen-and-paper reproduction - Lemma 5 equation (5) interval erase-upper equality

Status: checked finite-set equality.

This note strengthens the previous equation `(5)` inserted-set count.  It
identifies the single same-coordinate interval value not represented by the
lower endpoint plus strict Eq5 offsets.  It does not construct any displayed
source vector.

## Source

For a fixed coordinate `p`, Aoyagi Lemma 5 uses the same-coordinate interval

```text
I_p = {H : Htilde_p <= H <= Htilde'_p}.
```

Equation `(5)` uses strict offsets

```text
alpha = Htilde'_p + 1 - k,
1 <= alpha < p.
```

The strict Eq5 offset values are therefore

```text
Htilde'_p - alpha,  1 <= alpha <= p-1,
```

subject also to the interval bound `alpha <= Htilde'_p-Htilde_p`.

## Rising Region

Assume

```text
a <= ell,
1 <= p,
p <= a,
p <= ell-a.
```

Then the interval excess is

```text
Htilde'_p - Htilde_p = p.
```

The full interval values are

```text
Htilde_p, Htilde_p+1, ..., Htilde_p+p.
```

Since `Htilde'_p = Htilde_p+p`, the strict Eq5 offsets give

```text
Htilde'_p-1, ..., Htilde'_p-(p-1)
  = Htilde_p+1, ..., Htilde_p+p-1.
```

Inserting the lower endpoint adds `Htilde_p`.  Thus the inserted set is

```text
{Htilde_p, Htilde_p+1, ..., Htilde_p+p-1}
  = I_p \ {Htilde'_p}.
```

The upper endpoint itself is not in the inserted set.  It is not the lower
endpoint because the gap is `p>=1`, and it is not a strict offset value because
that would require `alpha=0`.

## Lean Targets

```text
aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
aoyagiLemma5Eq5_upperEndpoint_not_mem_insert_lowerEndpoint_offsets_of_le_min
aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
```

## Nonclaims

- No equation `(5)` displayed-vector construction.
- No claim that equations `(3)` or `(4)` realise the erased upper endpoint.
- No source-label legality, terminal `tilde t=0`, vector admissibility, chart
  sequence, Lemma 5 order count, pole order, normal crossings, or RLCT
  extraction.
