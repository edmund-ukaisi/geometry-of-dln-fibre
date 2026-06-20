# Pen-and-paper reproduction - Definition 3 selected-width upper label bound

Status: checked conditional source arithmetic.

This note isolates the part of Definition 3 that helps with Aoyagi Lemma 5
equation `(4)` label legality.  It proves only the upper label bound
`Htilde_p+1 <= W_(p+1)` under explicit Definition 3 inequalities.  It does
not prove the lower label bound, terminality, or a displayed-family theorem.

## Source

Aoyagi Definition 3 selects widths

```text
W_i = M(S_i),        i=1,...,ell+1,
```

and the selected values satisfy the strict inequality

```text
sum_i W_i > ell * W_j
```

for every selected value `W_j`.  It also defines the integer `M` and residue
`a` by

```text
sum_i W_i = ell*(M-1)+a,
0 <= a <= ell.
```

In the source situation `ell>=1`.

## Selected Width Bound

Fix a selected width `W_j`.  Suppose for contradiction that

```text
W_j >= M.
```

Multiplying by positive `ell` gives

```text
ell*W_j >= ell*M.
```

Since `a<=ell`,

```text
ell*M = ell*(M-1)+ell >= ell*(M-1)+a = sum_i W_i.
```

This contradicts the strict selected inequality `ell*W_j < sum_i W_i`.
Therefore

```text
W_j <= M-1.
```

## Equation (4) Upper Label Bound

For Aoyagi Lemma 5 equation `(4)`, write `p=j0`.  Under the printed lower-arm
guard `p<=a`, the lower Htilde value is

```text
Htilde_p = P_(p+1) - pM,
```

where

```text
P_(p+1) = W_1 + ... + W_(p+1).
```

The upper label bound for

```text
k = Htilde_p + 1
```

is

```text
Htilde_p + 1 <= W_(p+1).
```

Substituting the lower Htilde formula, this is equivalent to

```text
P_p + 1 <= pM.
```

If `p>=1` and every selected width is at most `M-1`, then

```text
P_p <= p(M-1),
P_p + 1 <= p(M-1)+1 <= pM.
```

Thus Definition 3's strict selected inequality proves the upper label bound
for equation `(4)`.

The lower label bound remains

```text
1 <= Htilde_p + 1,
```

equivalently

```text
pM <= P_(p+1).
```

This is not discharged by the selected-width upper bound.

## Lean Targets

```text
aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
aoyagiPrefixSum_sub_current_add_one_le_mul_of_selectedWidth_le_pred
aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_selectedWidth_le_pred
aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_sourceSelectedInequality
```

## Nonclaims

- This does not prove `1 <= Htilde_p+1`.
- This does not prove equation `(3)`'s one-unit slack guard `W_1+2<=M`.
- This does not construct equations `(3)` or `(4)` displayed source vectors.
- This does not prove `tilde t=0`, vector admissibility, Lemma 5 order count,
  normal crossings, or RLCT extraction.
