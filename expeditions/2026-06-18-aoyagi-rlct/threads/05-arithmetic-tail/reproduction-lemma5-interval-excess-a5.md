# Pen-and-paper reproduction - Lemma 5 interval-excess arithmetic

Status: checked sub-slice.  This reproduces only the elementary interval-size
sum appearing in Aoyagi's Lemma 5 on PDF pp. 25-26.  It does not reproduce the
chart-family construction, admissibility of the displayed vectors, pole order,
normal crossings, or RLCT extraction.

## Source Target

Aoyagi defines extremal sequences `Htilde_j` and `Htilde'_j`, then considers
intervals

```text
I_j = { H : Htilde_j <= H <= Htilde'_j }.
```

The source gives a piecewise interval size.  The useful arithmetic identity is
not the raw sum of `|I_j|`; it is the excess-cardinality sum

```text
1 + sum_{j=1}^{ell-1} (|I_j| - 1) = a(ell-a) + 1.
```

The leading `1` is the baseline contribution.  The summation over
`j=1,...,ell-1` matches the nontrivial free coordinates.  Including `j=ell`
would not change the sum because the endpoint excess is zero.

## Excess Formula

Let `c = ell-a`.  From the printed definitions of `Htilde` and `Htilde'`, the
common partial sum cancels in the difference:

```text
|I_j| - 1 = Htilde'_j - Htilde_j
          = min(j,a) - max(0,j-c).
```

Equivalently,

```text
|I_j| - 1 = min(j, ell-j, a, ell-a),
```

for `0 <= a <= ell`.  With

```text
m = min(a, ell-a),
n = max(a, ell-a),
```

this gives Aoyagi's displayed piecewise count:

```text
|I_j| = j+1                    for 1 <= j <= m,
|I_j| = m+1                    for m+1 <= j <= n,
|I_j| = m+1+n-j = ell+1-j      for n+1 <= j <= ell.
```

At `j=ell`, `|I_ell|=1`, so the excess is zero.

## Sum Identity

The excesses count a rectangle by diagonals.  Consider pairs

```text
(p,q),  0 <= p < a,  0 <= q < ell-a.
```

The level map is

```text
(p,q) |-> p+q+1.
```

The fiber at level `j` has cardinality

```text
min(j, ell-j, a, ell-a),
```

so summing all fibers counts the rectangle:

```text
sum_j (|I_j|-1) = a(ell-a).
```

The levels `j=0` and `j=ell` contribute zero in the closed excess formula, so
the source interval `j=1,...,ell-1` has the same excess sum:

```text
sum_{j=1}^{ell-1} (|I_j|-1) = a(ell-a).
```

Therefore

```text
1 + sum_{j=1}^{ell-1} (|I_j|-1) = a(ell-a)+1.
```

## Boundary Checks

- `a=0`: all intervals are singletons; excess sum is `0`; total is `1`.
- `a=ell`: all intervals are singletons; excess sum is `0`; total is `1`.
- `ell=1`: the source sum over `1..ell-1` is empty; the endpoint cases give
  total `1`.
- `ell=0`: the pure natural-number formula has an empty sum convention, but
  this is not source-facing because earlier Aoyagi formulas divide by `ell`.

## Lean Boundary

This supports only:

- a closed-form definition of the interval excess;
- a rectangle-fiber model for that excess;
- the finite sum identity over `j=1,...,ell-1`;
- the source-facing arithmetic form
  `1 + sum(intervalSize-1) = a(ell-a)+1`.

It does not prove Lemma 5.  The chart-family admissibility, coverage,
exclusions, and exact pole-order interpretation remain separate obligations.
