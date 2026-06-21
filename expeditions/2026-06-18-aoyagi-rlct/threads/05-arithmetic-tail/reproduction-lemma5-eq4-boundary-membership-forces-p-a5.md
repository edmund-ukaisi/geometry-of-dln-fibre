# Pen-and-paper reproduction - Lemma 5 equation (4) boundary membership forces p

Status: checked finite source-selected interval arithmetic.

This note records a necessary condition for the strict equation `(4)` boundary
value to lie in its own boundary-coordinate interval.  It is a consequence of
the already-reproduced width window and Definition 3's selected-width
inequality.

## Source

Aoyagi PDF p. 27, equation `(4)`, supplies the boundary value

```text
B = T(S_(p+ell-a+2)-1) = Htilde'_(p+ell-a) - p + 1.
```

In Lean's zero-based notation, for the strict boundary case set

```text
r = p+(ell-a)+1,
W_r = M(S_(r+1)).
```

The previous boundary-coordinate window reproduction proves

```text
B in [Htilde_r,Htilde'_r]
iff
M-p+1 <= W_r <= M-p+1+excess(ell,a,r).
```

## Calculation

Assume the source-selected hypotheses from Definition 3:

```text
sum_i W_i = ell*(M-1)+a,
ell*W_i < sum_j W_j  for every selected i.
```

Under `1<=ell` and `a<=ell`, the strict selected-width inequality gives

```text
W_i <= M-1
```

for every selected width.  In the strict equation `(4)` boundary case, the
supplied certificate has `a<=ell`, and `p+1<a` implies `1<=ell` and
`r<ell+1`, so this upper bound applies to `W_r`:

```text
W_r <= M-1.
```

If the boundary value is in the boundary-coordinate interval, the left edge of
the width window also gives

```text
M-p+1 <= W_r.
```

Combining,

```text
M-p+1 <= W_r <= M-1.
```

Canceling `M` gives

```text
2 <= p.
```

Equivalently, if `p<2`, then the strict equation `(4)` boundary value cannot
belong to the boundary-coordinate interval under Definition 3's
source-selected hypotheses.

## Lean Targets

```text
aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_forces_two_le_p_of_sourceSelected
aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_sourceSelected_of_p_lt_two
```

## Guard Check

- No separate `p<=ell-a` guard is needed.  That guard belongs to the earlier
  classifier at coordinate `p+(ell-a)`, not to the boundary block's own
  coordinate once a supplied equation `(4)` certificate is present.
- No separate `1<=ell` hypothesis is needed.  It follows from `p+1<a` and the
  supplied certificate field `a<=ell`.
- This is a necessary condition only.  It does not say that membership holds
  for all `p>=2`.

## Nonclaims

- This does not construct equation `(4)`'s displayed vector.
- This does not prove membership for `p>=2`.
- This does not prove terminal `tilde t=0`.
- This does not prove introduced-label status, a Case 1(2) chart sequence,
  vector admissibility, Lemma 5 order count, normal crossings, or RLCT
  extraction.
