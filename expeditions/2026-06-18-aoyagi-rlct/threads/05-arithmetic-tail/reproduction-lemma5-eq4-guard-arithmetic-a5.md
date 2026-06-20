# Pen-and-paper reproduction - Lemma 5 equation (4) guard arithmetic

Status: checked conditional guard arithmetic.

This note records the finite arithmetic around Aoyagi Lemma 5 equation `(4)`.
It does not prove that the displayed vector is a legal, terminal, admissible
source-family member.

## Source

Aoyagi PDF p. 27, equation `(4)`, has

```text
s = S_(j0+1)-1,
k = Htilde_j0 + 1,
j0 <= a.
```

The displayed tail also contains a cutoff of the form

```text
S_(j0 + ell-a + 2).
```

Definition 3 supplies selected indices only as

```text
S_1,...,S_(ell+1).
```

Write `p=j0`, `c=ell-a`, and write the selected widths as

```text
W_i = M(S_i).
```

In Lean's zero-based convention, `W_(p+1)` is
`aoyagiSelectedWidthNat ell m p`, and the inclusive prefix

```text
P_(p+1) = W_1 + ... + W_(p+1)
```

is `aoyagiPrefixSum (aoyagiSelectedWidthNat ell m) p`.

## Interval Excess

The already-formalised interval excess is

```text
e_p = min(p, ell-p, a, ell-a).
```

If

```text
p <= a,
p <= ell-a,
```

then `2p <= ell`, hence `p <= ell-p`, and therefore

```text
e_p = p.
```

This is now exposed as the reusable Lean lemma
`aoyagiLemma5IntervalExcess_eq_self_of_le_min`.

## Selected Index Guard

The displayed cutoff `S_(p+c+2)` is defined from Definition 3 exactly when

```text
p+c+2 <= ell+1.
```

Substituting `c=ell-a` and assuming `a<=ell`, this is equivalent to

```text
p+1 <= a.
```

Thus the printed guard `p<=a` is one unit too weak at `p=a`, where the formula
would ask for `S_(ell+2)`.

## Label Bounds

For `p<=a`, the lower displayed chain is

```text
L_p = P_(p+1) - pM.
```

The label in equation `(4)` is

```text
k = L_p + 1.
```

The bounds `1 <= k <= W_(p+1)` are equivalent to:

```text
1 <= P_(p+1) - pM + 1,
P_(p+1) - pM + 1 <= W_(p+1).
```

These rearrange to

```text
pM <= P_(p+1),
P_(p+1) - W_(p+1) + 1 <= pM.
```

Equivalently, the threshold `pM` lies between the previous selected-width
prefix and the current selected-width prefix:

```text
P_p < pM <= P_(p+1).
```

The right inequality is a genuine nonnegativity/admissibility condition for
`L_p`.  It is not proved by the displayed Htilde formulas alone.

## Lean Targets

```text
aoyagiLemma5IntervalExcess_eq_self_of_le_min
aoyagiLemma5Eq4_selectedIndexGuard_iff
aoyagiHtildeLowerNat_add_one_labelBounds_iff_prefixCrossing
```

## Nonclaims

- No equation `(4)` displayed source vector is constructed.
- No source label is proved legal from Definition 3 alone.
- No `tilde t=0` terminal condition is proved.
- No vector admissibility, chart-family coverage, Lemma 5 order count, pole
  order, normal crossings, or RLCT extraction is proved.
