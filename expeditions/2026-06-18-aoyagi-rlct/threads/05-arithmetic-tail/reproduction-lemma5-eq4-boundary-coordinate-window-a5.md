# Pen-and-paper reproduction - Lemma 5 equation (4) boundary-coordinate window

Status: checked finite interval bookkeeping.

This note records the equation `(4)` strict-boundary value against the
same-coordinate interval at the boundary block's own coordinate.  This is
different from the previous classifier at coordinate `p+(ell-a)`.

## Source

Aoyagi PDF p. 27, equation `(4)`, assigns the special boundary

```text
S_(p+ell-a+2)-1
```

the value

```text
Htilde'_(p+ell-a) - p + 1.
```

In Lean's zero-based notation set

```text
c = ell-a,
j = p+c,
r = p+c+1,
W_r = M(S_(r+1)).
```

The supplied boundary value is

```text
B = T(C.point r - 1) = U_j - p + 1,
```

where `U_i = Htilde'_i`.

## Upper-Chain Increment

In the strict boundary case `p+1<a`, the boundary index is nonterminal:

```text
r < ell.
```

The upper displayed chain uses the low-first increment pattern, so after
coordinate `ell-a` its subtraction increment is `M`.  Therefore

```text
U_r = U_j + W_r - M.
```

Subtracting gives

```text
B - U_r = M - W_r - p + 1.
```

Equivalently,

```text
U_r - B = W_r + p - M - 1.
```

## Boundary-Coordinate Interval

The same-coordinate interval at coordinate `r` is

```text
L_r <= H <= U_r,
```

with gap

```text
U_r - L_r = excess(ell,a,r).
```

Thus `B` lies in this interval if and only if

```text
B <= U_r
and
L_r <= B.
```

Using the offset above, this is equivalent to

```text
M - p + 1 <= W_r
and
W_r <= M - p + 1 + excess(ell,a,r).
```

This is the boundary-coordinate width window.

## Reduced Excess

At

```text
r = p+(ell-a)+1,
```

the strict guard `p+1<a` reduces the interval excess to

```text
excess(ell,a,r) = min(ell-a, a-p-1).
```

Therefore the reduced window is

```text
M - p + 1 <= W_r <= M - p + 1 + min(ell-a,a-p-1).
```

## Source-Shaped `p=1` Consequence

Definition 3's strict selected-width inequalities imply every selected width
satisfies

```text
W_i <= M-1.
```

For `p=1`, the lower edge of the width window is `M`, so the selected-width
bound forces

```text
W_r <= M-1 < M.
```

Hence the boundary value is strictly above `U_r`, and so it is not in the
boundary-coordinate interval.

## Lean Targets

```text
aoyagiHtildeUpperNat_succ_eq_add_selectedWidthNat_sub_increment
aoyagiLemma5Eq4_boundaryCoordinate_intervalExcess_eq_min
aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate
aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow
aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow_min
aoyagiLemma5Eq4_boundaryValue_gt_boundaryUpper_of_p1_sourceSelected
aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_p1_sourceSelected
```

## Nonclaims

- This does not construct equation `(4)`'s displayed vector.
- This does not prove terminal `tilde t=0`.
- This does not prove introduced-label status, a Case 1(2) chart sequence,
  vector admissibility, Lemma 5 order count, normal crossings, or RLCT
  extraction.
- This does not classify the previously proved coordinate `p+(ell-a)` case;
  that is a separate interval classifier.
