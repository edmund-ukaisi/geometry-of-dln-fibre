# Pen-and-paper reproduction - Lemma 5 equation (5) source label

Status: checked conditional source-label legality.

This note records the elementary finite arithmetic proving that Aoyagi Lemma 5
equation `(5)`'s own-coordinate label is legal once the selected-width
hypotheses and actual-width compatibility are supplied.  It does not construct
the displayed vector or prove terminal `tilde t=0`.

## Source

Aoyagi Definition 3, PDF pp. 8-9, supplies selected widths `W_i=M(S_i)`, the
selected sum

```text
sum_i W_i = ell*(M-1)+a,
```

and the strict selected-width inequalities.  Aoyagi Lemma 5 equation `(5)`,
PDF p. 27, supplies

```text
alpha = Htilde'_(j0)+1-k,
S_(j0+1)-1 <= s < S_(j0+2)-1,
Htilde_(j0)+1 <= k < Htilde'_(j0)+1,
j0 > alpha.
```

## Zero-Based Translation

Lean uses

```text
C.point p = S_(p+1),
C.block p s iff S_(p+1)-1 <= s < S_(p+2)-1.
```

Thus paper `j0` is Lean coordinate `p`, and the selected width at the own
coordinate is

```text
W_p = aoyagiSelectedWidthNat ell m p = M(S_(p+1)).
```

The source label relation is

```text
k = Htilde'_p + 1 - alpha.
```

The printed source guard

```text
Htilde_p + 1 <= k < Htilde'_p + 1
```

is equivalently represented by

```text
1 <= alpha,
alpha <= Htilde'_p - Htilde_p.
```

Lean encodes the second inequality as

```text
alpha <= aoyagiLemma5IntervalExcess ell a p.
```

## Label Bounds

Let

```text
P_p = W_0 + ... + W_p.
```

Definition 3's strict selected-width inequalities imply

```text
W_i <= M-1
```

for every selected coordinate.  Therefore the tail after `p` has at most
`(ell-p)*(M-1)`, and the selected sum gives

```text
P_p >= p*(M-1)+a.
```

Since `min(p,a)<=a`,

```text
Htilde_p
  = P_p - (p*(M-1)+min(p,a))
  >= 0.
```

So `Htilde_p+1>=1`.

For the upper bound, the previous prefix satisfies

```text
P_p - W_p = W_0 + ... + W_(p-1) <= p*(M-1).
```

The upper-chain subtraction is

```text
p*(M-1)+upperHigh_p,
```

with `upperHigh_p>=0`, hence

```text
Htilde'_p <= W_p.
```

Now

```text
k = Htilde'_p + 1 - alpha.
```

From `alpha <= Htilde'_p-Htilde_p`, we get

```text
k >= Htilde_p+1 >= 1.
```

From `1<=alpha`, we get

```text
k <= Htilde'_p <= W_p.
```

Thus

```text
1 <= k <= W_p.
```

If additionally the actual layer width agrees with the selected width,

```text
n((C.point p - 1)+1) = W_p,
```

then `k` is an `actualWidthLabel` at source layer `C.point p - 1`.

## Lean Targets

```text
aoyagiHtildeLowerIncrementPrefix_le_prefixSum_of_selectedWidth_le_pred
aoyagiHtildeLowerNat_add_one_pos_any_of_sourceSelectedInequality
aoyagiPrefixSum_sub_current_le_mul_pred_of_selectedWidth_le_pred
aoyagiHtildeUpperNat_le_selectedWidth_of_selectedWidth_le_pred
aoyagiHtildeUpperNat_le_selectedWidth_of_sourceSelectedInequality
aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality
aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility
aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel
```

## Nonclaims

- No construction or existence proof for equation `(5)`'s displayed vector.
- No terminal `tilde t=0` theorem.
- No full vector admissibility or source-vector-to-chain correspondence.
- No Case 1(2) chart sequence.
- No Lemma 5 chart-family order count.
- No pole order, normal crossings, or RLCT extraction.
