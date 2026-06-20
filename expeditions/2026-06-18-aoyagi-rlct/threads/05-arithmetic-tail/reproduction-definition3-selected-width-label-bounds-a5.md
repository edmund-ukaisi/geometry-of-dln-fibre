# Pen-and-paper reproduction - Definition 3 selected-width label bounds

Status: checked source arithmetic.

This note extends the previous upper-label calculation for Aoyagi Lemma 5
equation `(4)`.  It proves both label inequalities for
`k=Htilde_p+1` from Definition 3's selected-width hypotheses.  It still does
not construct the displayed source vector or prove terminality.

## Source

Aoyagi Definition 3 selects widths

```text
W_i = M(S_i),        i=1,...,ell+1,
```

with selected total

```text
B = sum_i W_i = ell*(M-1)+a,      0 <= a <= ell,
```

and strict selected inequality

```text
ell*W_i < B
```

for every selected width.  In Lemma 5 equation `(4)`, for `p=j0<=a`,

```text
Htilde_p = P_(p+1) - pM,
k = Htilde_p + 1,
```

where `P_r = W_1+...+W_r`.

## Width Bound

As in the previous note, the strict selected inequality forces

```text
W_i <= M-1
```

for every selected width.  If `W_i>=M`, then

```text
ell*W_i >= ell*M = ell*(M-1)+ell >= ell*(M-1)+a = B,
```

contradicting `ell*W_i<B`.

## Lower Label Bound

The lower label bound is

```text
1 <= Htilde_p + 1,
```

equivalently

```text
pM <= P_(p+1).
```

The tail after `P_(p+1)` has `ell-p` terms.  Since every selected width is at
most `M-1`,

```text
B - P_(p+1) <= (ell-p)(M-1).
```

Using `B=ell*(M-1)+a`,

```text
P_(p+1)
  >= ell*(M-1)+a - (ell-p)(M-1)
   = p*(M-1)+a.
```

Since `p<=a`,

```text
p*(M-1)+a >= p*(M-1)+p = pM.
```

Therefore

```text
pM <= P_(p+1),
```

and hence `1<=Htilde_p+1`.

## Upper Label Bound

The upper label bound is

```text
Htilde_p + 1 <= W_(p+1),
```

equivalently

```text
P_p + 1 <= pM.
```

If `1<=p`, the previous prefix has `p` terms, each at most `M-1`, so

```text
P_p + 1 <= p(M-1)+1 <= pM.
```

This is the previously landed upper-label calculation.

## Lean Targets

```text
aoyagiPrefixSum_mul_le_of_selectedWidth_le_pred
aoyagiPrefixSum_mul_le_of_sourceSelectedInequality
aoyagiHtildeLowerNat_add_one_pos_of_selectedWidth_le_pred
aoyagiHtildeLowerNat_add_one_pos_of_sourceSelectedInequality
aoyagiHtildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
```

## Nonclaims

- This does not construct the equation `(4)` displayed source vector.
- This does not repair the selected-index guard; the displayed cutoff still
  needs `p+1<=a` unless an external `S_(ell+2)` convention is supplied.
- This does not prove the own-coordinate guard `p<=ell-a`.
- This does not prove terminal `tilde t=0`, vector admissibility, chart-family
  coverage, Lemma 5 order count, normal crossings, or RLCT extraction.
