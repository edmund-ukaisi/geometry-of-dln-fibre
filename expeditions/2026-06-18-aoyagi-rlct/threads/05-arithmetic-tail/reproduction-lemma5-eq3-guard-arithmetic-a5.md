# Pen-and-paper reproduction - Lemma 5 equation (3) guard arithmetic

Status: checked conditional guard arithmetic.

This note records the finite arithmetic around Aoyagi Lemma 5 equation `(3)`.
It does not prove that the displayed exceptional vector is legal, terminal,
admissible, or part of a chart-family construction.

## Source

Aoyagi PDF p. 27, equation `(3)`, has the exceptional label

```text
s = S_2-1,
k = Htilde'_1 + 1.
```

The displayed vector also contains a special cutoff

```text
S_(ell-a+2).
```

Definition 3 supplies selected indices only as

```text
S_1,...,S_(ell+1).
```

Write selected widths as

```text
W_i = M(S_i).
```

In Lean's zero-based convention, `W_1` is
`aoyagiSelectedWidthNat ell m 0`, and `W_2` is
`aoyagiSelectedWidthNat ell m 1`.

## Selected Index Guard

The displayed cutoff `S_(ell-a+2)` is defined from Definition 3 exactly when

```text
ell-a+2 <= ell+1.
```

Assuming `a<=ell`, this is equivalent to

```text
1 <= a.
```

Thus equation `(3)` has an explicit lower-interior guard: if `a=0`, the
special cutoff asks for an index beyond the selected list.

## First Upper-Lower Gap

The already-formalised gap formula is

```text
Htilde'_j - Htilde_j = min(j, ell-j, a, ell-a).
```

At `j=1`, if

```text
1 <= a,
a < ell,
```

then the minimum is `1`, so

```text
Htilde'_1 - Htilde_1 = 1.
```

This is the arithmetic reason that the exceptional source label
`Htilde'_1+1` sits one step above the lower endpoint in the interior case.

## Label Bounds

When `a<ell`, the first upper Htilde value is

```text
Htilde'_1 = W_1 + W_2 - (M-1).
```

Thus the label in equation `(3)` is

```text
k = Htilde'_1 + 1 = W_1 + W_2 - M + 2.
```

The source label bounds at `s=S_2-1` are

```text
1 <= k <= W_2.
```

These are equivalent to

```text
M-1 <= W_1 + W_2,
W_1 + 2 <= M.
```

The second inequality is the one-unit slack condition not supplied by the
displayed Htilde formulas alone.

## Lean Targets

```text
aoyagiLemma5Eq3_selectedIndexGuard_iff
aoyagiHtildeUpperNat_one_sub_lowerNat_one_of_pos_of_lt
aoyagiHtildeUpperNat_one_add_one_labelBounds_iff_widthGuards
```

## Nonclaims

- No equation `(3)` displayed source vector is constructed.
- No source label is proved legal from Definition 3 alone.
- No `tilde t=0` terminal condition is proved.
- No vector admissibility, chart-family coverage, Lemma 5 order count, pole
  order, normal crossings, or RLCT extraction is proved.
