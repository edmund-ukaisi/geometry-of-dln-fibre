# Pen-and-paper reproduction - Lemma 5 equation (5) own-coordinate offset

Status: checked supplied own-coordinate branch.

This note records a conservative finite slice of Aoyagi Lemma 5 equation
`(5)`.  It does not construct the displayed vector or prove terminal
`tilde t=0`.

## Source

Aoyagi PDF p. 27, equation `(5)`, is for

```text
alpha = Htilde'_(j0) + 1 - k,
S_(j0+1)-1 <= s < S_(j0+2)-1,
Htilde_(j0)+1 <= k < Htilde'_(j0)+1,
j0 > alpha.
```

The branch relevant to the own coordinate is the fourth displayed branch:

```text
T(S) = Htilde'_(j-1) - alpha + 1 - (j-j0)
```

for

```text
j0 < j <= j0 + (a-alpha) + 1.
```

## Zero-Based Translation

The Lean selected-cutpoint convention is

```text
C.point b = S_(b+1),
C.block b S iff S_(b+1)-1 <= S < S_(b+2)-1.
```

Thus the paper parameter `j0` is Lean coordinate `p`, not `p+1` and not
`p-1`.  The own coordinate `s` lies in `C.block p s`, which is the paper block
`j=p+1`.

Substituting `j=p+1` into the fourth branch gives

```text
T(s) = Htilde'_p - alpha + 1 - ((p+1)-p)
     = Htilde'_p - alpha.
```

Using the label relation

```text
k = Htilde'_p + 1 - alpha,
```

this is also

```text
T(s) = k - 1.
```

## Interval Membership

The same-coordinate interval at coordinate `p` is

```text
Htilde_p <= H <= Htilde'_p.
```

The already-formalised gap formula is

```text
Htilde'_p - Htilde_p = excess(ell,a,p),
```

where

```text
excess(ell,a,p) = min(p, ell-p, a, ell-a).
```

If

```text
alpha <= excess(ell,a,p),
```

then

```text
Htilde'_p - alpha >= Htilde'_p - excess(ell,a,p) = Htilde_p.
```

Since `alpha` is a natural number,

```text
Htilde'_p - alpha <= Htilde'_p.
```

Therefore the own-coordinate value lies in the same-coordinate interval.

## Offset Count

The finite offset family allowed by this narrow same-coordinate/source guard is

```text
1 <= alpha <= min(excess(ell,a,p), p-1).
```

The realised values are

```text
Htilde'_p - alpha.
```

The map `alpha |-> Htilde'_p - alpha` is injective.  Hence the finite image has
cardinality

```text
min(excess(ell,a,p), p-1).
```

This count is only a count of same-coordinate offset values for the supplied
own-coordinate branch.  It is not the Lemma 5 chart-family order count.

## Lean Targets

```text
AoyagiLemma5Eq5OwnCoordinateBranch
aoyagiLemma5Eq5OffsetValueSet
aoyagiLemma5Eq5_offsetValue_injective
aoyagiLemma5Eq5OffsetValueSet_card
aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat
aoyagiLemma5Eq5_ownCoordinate_value
aoyagiLemma5Eq5_ownCoordinate_eq_label_pred
aoyagiLemma5Eq5_ownCoordinate_mem_intervalValueSetNat
aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet
```

## Nonclaims

- No construction or existence proof for equation `(5)`'s displayed vector.
- No source-label legality proof for `k`.
- No full selected-span classifier for equation `(5)`.
- No terminal `tilde t=0` theorem.
- No vector admissibility or source-vector-to-chain correspondence.
- No Case 1(2) chart sequence.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

For a full selected-span equation `(5)` classifier, the final cutoff
`S_(p+(a-alpha)+2)` needs the explicit selected-range guard

```text
p + (a-alpha) + 1 <= ell.
```
