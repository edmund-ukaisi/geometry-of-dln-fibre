# Pen-and-paper reproduction - Lemma 5 equation (4) interval classifier

Status: checked finite interval bookkeeping.

This note records a finite consequence of Aoyagi Lemma 5 equation `(4)`: in
the strict boundary case, the special boundary value is not uniformly outside
the same-coordinate interval family.  At coordinate `p+(ell-a)`, membership is
controlled exactly by the inequality `2*p <= a+1`.

## Source

Aoyagi PDF p. 27, equation `(4)`, assigns the special boundary

```text
S_(p+ell-a+2)-1
```

the value

```text
Htilde'_(p+ell-a) - p + 1.
```

In Lean's zero-based selected-cutpoint notation this is

```text
T(C.point (p+(ell-a)+1)-1) = Htilde'_(p+(ell-a)) - p + 1.
```

The strict boundary guard is `p+1<a`; together with `p<=ell-a`, the coordinate

```text
j = p+(ell-a)
```

is a valid selected coordinate.

## Same-Coordinate Interval

The same-coordinate interval at coordinate `j` is

```text
Htilde_j <= H <= Htilde'_j.
```

For the equation `(4)` special boundary value, the upper-bound side is

```text
Htilde'_j - p + 1 <= Htilde'_j,
```

which follows from `1<=p`.

The lower-bound side is

```text
Htilde_j <= Htilde'_j - p + 1.
```

Using the already-formalised gap formula

```text
Htilde'_j - Htilde_j = excess(ell,a,j),
```

this is equivalent to

```text
p - 1 <= excess(ell,a,j).
```

## Excess Calculation

The interval excess is

```text
excess(ell,a,j) = min(j, ell-j, a, ell-a).
```

At `j=p+(ell-a)`, the hypotheses `a<=ell`, `p+1<a`, and `p<=ell-a` give

```text
ell-j = a-p
```

and the nested minimum reduces to

```text
excess(ell,a,p+(ell-a)) = min(ell-a, a-p).
```

Since `p<=ell-a`, the condition `p-1 <= min(ell-a,a-p)` is equivalent to

```text
p - 1 <= a - p,
```

and hence to

```text
2*p <= a+1.
```

Therefore

```text
T(C.point (p+(ell-a)+1)-1) in intervalValueSet(j)
iff 2*p <= a+1.
```

## False Stronger Claim

Equation `(3)` has a uniform same-coordinate interval obstruction because its
special boundary value is `Htilde'_j+1`.  Equation `(4)` does not have an
analogous uniform obstruction at coordinate `p+(ell-a)`: the value is below,
at, or above the lower endpoint according to whether the excess reaches
`p-1`.

Thus the source-faithful theorem is a classifier, not a nonmembership theorem.

## Lean Targets

```text
aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_iff_two_mul_le
aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_of_two_mul_le
aoyagiLemma5Eq4_boundaryValue_not_mem_intervalValueSetNat_of_lt_two_mul
```

## Nonclaims

- This does not construct equation `(4)`'s displayed vector.
- This does not prove terminal `tilde t=0`.
- This does not prove introduced-label status, a Case 1(2) chart sequence,
  vector admissibility, Lemma 5 order count, normal crossings, or RLCT
  extraction.
- This does not claim a uniform interval obstruction for all strict equation
  `(4)` boundary values.
